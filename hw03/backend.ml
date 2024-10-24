(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
  function
    | Null -> (Movq, [Imm (Lit 0L); dest])
    | Const x -> (Movq, [Imm (Lit x); dest])
    | Gid lbl -> (Movq, [Imm (Lbl lbl); dest])
    | Id uid -> (Movq, [lookup ctxt.layout uid; dest])


(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)


let compile_call (ctxt:ctxt) ((ret_ty, fn_op, args) : Ll.ty * Ll.operand * (Ll.ty * Ll.operand) list) dst : ins list =
  let reg_args = [Rdi; Rsi; Rdx; Rcx; R08; R09] in
  let push_arg (arg_ty, arg_op) = match arg_op with
    | Null -> [(Pushq, [Imm (Lit 0L)])]
    | Const v -> [(Pushq, [Imm (Lit v)])]
    | Gid _ -> failwith "compile_call: Labels cannot be used as operands"
    | Id uid -> [(Pushq, [lookup ctxt.layout uid])]
  in
  let setup_args = List.mapi (fun i arg ->
    if i < List.length reg_args then
      [compile_operand ctxt (Reg (List.nth reg_args i)) (snd arg)]
    else push_arg arg) args
  in
  let teardown_args =
    let stack_args_count = max 0 (List.length args - List.length reg_args) in
    if stack_args_count > 0 then
      [(Addq, [Imm (Lit (Int64.of_int (stack_args_count * 8))); Reg Rsp])]
    else []
  in
  let call_instr = [compile_operand ctxt (Reg Rax) fn_op; (Callq, [Reg Rax])] in
  let store_ret = match ret_ty with
    | Void -> []
    | _ -> [(Movq, [Reg Rax; lookup ctxt.layout dst])]
  in
  List.concat [List.flatten setup_args; call_instr; teardown_args; store_ret]


(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty tdecls t : int =
  match t with
    | Void | I8 | Fun _ -> 0
    | I1 | I64 | Ptr _ -> 8
    | Struct tys -> List.fold_left (fun acc x -> acc + (size_ty tdecls x)) 0 tys
    | Array (i, ty) -> i * (size_ty tdecls ty)
    | Namedt tid -> size_ty tdecls (lookup tdecls tid)


(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) (path: Ll.operand list) dst : ins list =
  let (op_ty, op_op) = op in
  begin match (op_ty, path) with
    | (Ptr top_type, ary::path_rem) -> begin
      let top_size = Int64.of_int (size_ty ctxt.tdecls top_type) in
      let rec process_path (ty:Ll.ty) (path: Ll.operand list) : ins list =
        match (ty, path) with
          | (Namedt nty, path_rem) -> process_path (lookup ctxt.tdecls nty) path_rem
          | (Struct tys, (Const entry)::path_rem) -> begin
            let rec nthsum i (list:Ll.ty list) = match (i, list) with
              | (0L, entry::_) -> (0L, entry)
              | (i, entry::rem) -> 
                let (acc, res) = nthsum (Int64.sub i 1L) rem in 
                (Int64.add acc (Int64.of_int (size_ty ctxt.tdecls entry)), res)
              | _ -> failwith "compile_gep: Failed to find nth"
            in
            let (elem_offset, ty) = nthsum entry tys 
            in
            (Addq, [Imm (Lit elem_offset); Reg R08])::(process_path ty path_rem)
            end
          | (Array (_, aty), index::path_rem) -> begin
            let entry_size = Int64.of_int (size_ty ctxt.tdecls aty) in
            (compile_operand ctxt (Reg R09) index)::(Imulq, [Imm (Lit entry_size); Reg R09])::(Addq, [Reg R09; Reg R08])::(process_path aty path_rem)
            end
          | (_, []) -> []
          | (ty, rem) -> failwith ("compile_gep: Failed to match gep path " ^ (Llutil.string_of_ty ty) ^ " [" ^ (List.fold_left (^) "" (List.map (Llutil.string_of_operand) rem)) ^ "]")
      in
      (compile_operand ctxt (Reg R08) op_op)::(compile_operand ctxt (Reg R09) ary)::(Imulq, [Imm (Lit top_size); Reg R09])::(Addq, [Reg R09; Reg R08])::(process_path top_type path_rem)
      end
    | _ -> failwith "compile_gep: Gep type was not pointer or path is empty"
  end @ [Movq, [Reg R08; lookup ctxt.layout dst]]


(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  match i with
    | Binop (bop, ty, op1, op2) -> 
        let ins1 = compile_operand ctxt (Reg R08) op1 in
        let ins2 = compile_operand ctxt (Reg Rcx) op2 in
        let binop_ins = 
          begin match bop with
            | Add -> (Addq, [Reg Rcx; Reg R08])
            | Sub -> (Subq, [Reg Rcx; Reg R08])
            | Mul -> (Imulq, [Reg Rcx; Reg R08])
            | Shl -> (Shlq, [Reg Rcx; Reg R08])
            | Lshr -> (Shrq, [Reg Rcx; Reg R08])
            | Ashr -> (Sarq, [Reg Rcx; Reg R08])
            | And -> (Andq, [Reg Rcx; Reg R08])
            | Or -> (Orq, [Reg Rcx; Reg R08])
            | Xor -> (Xorq, [Reg Rcx; Reg R08])
          end in
        [ins1; ins2; binop_ins; (Movq, [Reg R08; lookup ctxt.layout uid])]
    | Icmp (cnd, ty, op1, op2) -> 
        let ins1 = compile_operand ctxt (Reg R08) op1 in
        let ins2 = compile_operand ctxt (Reg Rcx) op2 in
        let cmp_ins = (Cmpq, [Reg Rcx; Reg R08]) in
        let set_ins = 
          (Set (begin match cnd with
            | Eq -> X86.Eq
            | Ne -> X86.Neq
            | Slt -> X86.Lt
            | Sle -> X86.Le
            | Sgt -> X86.Gt
            | Sge -> X86.Ge
              end)
          , [Reg R09]) in
        [ins1; ins2; (Movq, [Imm (Lit 0L); Reg R09]); cmp_ins; set_ins; (Movq, [Reg R09; lookup ctxt.layout uid])]
    | Alloca ty -> 
        [(Subq, [Imm (Lit (Int64.of_int (size_ty ctxt.tdecls ty))); Reg Rsp]); (Movq, [Reg Rsp; lookup ctxt.layout uid])]
    | Load (ty, op) -> 
        [compile_operand ctxt (Reg R08) op; (Movq, [Ind2 R08; Reg R09]); (Movq, [Reg R09; lookup ctxt.layout uid])]
    | Store (ty, op1, op2) -> 
        [compile_operand ctxt (Reg R09) op1; compile_operand ctxt (Reg R08) op2; (Movq, [Reg R09; Ind2 R08])]
    | Call (ty, op, ops) -> 
        compile_call ctxt (ty, op, ops) uid
    | Bitcast (ty, op, ty2) -> 
        [compile_operand ctxt (Reg R08) op; (Movq, [Reg R08; lookup ctxt.layout uid])]
    | Gep (ty, op, ops) -> 
        compile_gep ctxt (ty, op) ops uid


(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are 
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  let rsp_to_rbp = [Movq, [Reg Rbp; Reg Rsp]; Popq, [Reg Rbp]] in
  let compile_ret op = 
    (match op with
      | Some operand -> [compile_operand ctxt (Reg Rax) operand]
      | None -> []) @ rsp_to_rbp @ [Retq, []]
  in
  match t with
  | Ret (Void, _) -> compile_ret None
  | Ret (_, operand) -> compile_ret operand
  | Br lbl -> [Jmp, [Imm (Lbl (mk_lbl fn lbl))]]
  | Cbr (op, true_lbl, false_lbl) ->
      [compile_operand ctxt (Reg R08) op;
       Cmpq, [Imm (Lit 0L); Reg R08];
       J Eq, [Imm (Lbl (mk_lbl fn false_lbl))];
       Jmp, [Imm (Lbl (mk_lbl fn true_lbl))]]


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. 
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  let {insns=insns; term=(uid, term) } = blk in
  let instructions : X86.ins list = List.concat (List.map (fun instr -> compile_insn ctxt instr) insns) in
  instructions @ (compile_terminator fn ctxt term)

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  match n with
    | 0 -> Reg Rdi
    | 1 -> Reg Rsi
    | 2 -> Reg Rdx
    | 3 -> Reg Rcx
    | 4 -> Reg R08
    | 5 -> Reg R09
    | _ -> Ind3 (Lit (Int64.of_int ((n - 4) * 8)), Rbp)


(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)

(* The function to calculate the stack layout *)
let stack_layout (args : uid list) ((block, lbled_blocks) : cfg) : int * layout =
  let assign_arg_locations args =
    List.mapi (fun i arg ->
      if i < 6 then
        (arg, Ind3 (Lit (Int64.of_int (-(i + 1) * 8)), Rbp))
      else
        (arg, arg_loc i)
    ) args
  in
  let initial_offset = -((min (List.length args) 6) + 1) * 8 in
  let instructions = 
    let extract_insns block = block.insns in
    List.concat (extract_insns block :: List.map (fun (_, block) -> extract_insns block) lbled_blocks)
  in
  let rec calculate_layout offset layout = function
    | [] -> (offset, layout)
    | (uid, insn) :: insns ->
        let size = match insn with
          | Binop (_, I64, _, _) -> 8
          | Alloca _ -> 8
          | Load (Ptr(_), _) -> 8
          | Store _ -> 0
          | Icmp _ -> 8
          | Call (Void, _, _) -> 0
          | Call _ -> 8
          | Bitcast (Ptr _, _, Ptr _) -> 8
          | Gep _ -> 8
          | _ -> failwith "stack_layout: Invalid type"
        in
        if size > 0 then
          let new_offset = offset - size in
          let new_layout = (uid, Ind3 (Lit (Int64.of_int offset), Rbp)) :: layout in
          calculate_layout new_offset new_layout insns
        else
          calculate_layout offset layout insns
  in
  let arg_layout = assign_arg_locations args in
  calculate_layout initial_offset arg_layout instructions

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_ty; f_param; f_cfg }:fdecl) : X86.prog =
  let mangled_name = Platform.mangle name in
  let (stack_offset, layout) = stack_layout f_param f_cfg in
  let ctxt = { tdecls; layout } in
  let setup_stack = [
    Pushq, [Reg Rbp];
    Movq, [Reg Rsp; Reg Rbp];
    Addq, [Imm (Lit (Int64.of_int stack_offset)); Reg Rsp]
  ] in
  let copy_args = List.mapi (fun i arg -> if i < 6 then [Movq, [arg_loc i; lookup layout arg]] else []) f_param |> List.concat in
  let compile_block_with_ctxt = compile_block mangled_name ctxt in
  let entry_elem = Asm.gtext (Platform.mangle mangled_name) (setup_stack @ copy_args @ compile_block_with_ctxt (fst f_cfg)) in
  let interior_elems = List.map (fun (lbl, block) -> compile_lbl_block mangled_name lbl ctxt block) (snd f_cfg) in
  entry_elem :: interior_elems


(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
