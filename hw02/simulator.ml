(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)

type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false 

(**************************************************************************************)

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x -> 
  begin match x with
  | Eq -> fz
  | Neq -> not fz
  | Gt -> not fz && (fs = fo)
  | Ge -> fs = fo
  | Lt -> fs <> fo
  | Le -> fz || (fs <> fo)
  end
 
(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option=
  if (addr >= mem_bot) && (addr < mem_top) then
    Some (Int64.to_int (Int64.sub addr mem_bot))
  else
    None

(* Determine the sign of a 64-bit integer *)
let sign (r:int64) : bool =
  (Int64.shift_right_logical r 63) = 1L

(* Rip increment *)
let rip_incr (m:mach) : unit =
  let pre_rip = m.regs.(rind Rip) in
  m.regs.(rind Rip) <- Int64.add pre_rip ins_size

(* Combine virtual address `v` with an offset and find the index of the combined address. *)
let set_addr (v:int64) (offset:int64) : int =
  begin match map_addr (Int64.add v offset) with
  | Some s -> s
  | None -> raise X86lite_segfault
  end

(* Extracting literals and avoiding labels *)
let get_lit (i:imm) : int64 =
  begin match i with 
  | Lit l -> l
  | Lbl _ -> invalid_arg "get_lit: Tried to interpret label"
  end

(* Return int64 value from the specified memory location *)
let value_of_mem (m: mach) (addr: quad): int64 =
  let open Array in
  match map_addr addr with
  | Some i -> int64_of_sbytes (to_list (sub m.mem i 8))
  | None   -> invalid_arg "value_of_men: bad address"

(* Return the value of an operand as an int64 *)
let get_value (m:mach) (opnd:operand) : int64 =
  begin match opnd with
  | Reg r -> m.regs.(rind r)
  | Imm i -> get_lit i
  | Ind1 i -> value_of_mem m (get_lit i)
  | Ind2 r -> value_of_mem m (m.regs.(rind r))
  | Ind3 (i,r) -> value_of_mem m (Int64.add m.regs.(rind r) (get_lit i))
  end

(* Store the value of an operand in memory *)
let store_value (v:int64) (opnd:operand) (m:mach) : unit =
  let v_bytes = Array.of_list (sbytes_of_int64 v) in
  let len = Array.length v_bytes in 
  match opnd with
  | Reg r -> 
    m.regs.(rind r) <- v
  | Ind1 i -> 
    Array.blit v_bytes 0 m.mem (set_addr (get_lit i) 0L) len
  | Ind2 r -> 
    Array.blit v_bytes 0 m.mem (set_addr m.regs.(rind r) 0L) len
  | Ind3 (i, r) -> 
    Array.blit v_bytes 0 m.mem (set_addr m.regs.(rind r) (get_lit i)) len
  | _ -> 
    failwith "store_value: Not register / valid address"

(* Update flags *)
let update_flags (f:flags) (fo:bool) (fs:bool) (fz:bool) : unit =
  begin
    f.fo <- fo;
    f.fs <- fs;
    f.fz <- fz
  end

(*  Convert arithmetic operation function with one argument to two *)
let one_arg_to_two (f) =
  let g (x) (y) = f x in g

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit =
  (* Execute instruction, update registers/memory and update flags*)
  let execute_ins (inst:ins) (m:mach) : unit =
    let open Int64_overflow in
    let optr, operand_list = inst in

    let handle_arith op =
      let src, dest, value, overflow =
        match operand_list with
        | s::d::[] ->
            let src = get_value m s in
            let dest = get_value m d in
            let result = op dest src in
            store_value result.value d m;
            (src, dest, result.value, result.overflow)
        | s::[] ->
            let src = get_value m s in
            let result = op src 0L in
            store_value result.value s m;
            (src, 0L, result.value, result.overflow)
        | _ -> failwith "handle_arith: More than two operands in this list"
      in
      rip_incr m;
      update_flags m.flags overflow (sign value) (value = Int64.zero) in
    
    let handle_logic op =
      let res =
          rip_incr m;
          begin match operand_list with
          | s::d::[] -> 
              let src = get_value m s in
              let dest = get_value m d in
              let result = op src dest in 
              store_value result d m;
              (src, dest, result, false)
          | s::[] -> 
              let src = get_value m s in
              let result = op src 0L in 
              store_value result s m;
              (src, 0L, result, false)
          | _ -> failwith "More than two operands in this list"
          end
      in
      let _, _, value, overflow = res in
      update_flags m.flags overflow (sign value) (value = Int64.zero) in

    let handle_shift op cond =
      match operand_list with
      | amt::d::[] ->
        let s = 
          begin match amt with
          | Imm i -> Int64.to_int (get_lit i)
          | Reg Rcx -> Int64.to_int (m.regs.(rind Rcx))
          | _ -> failwith "handle_shift: Shifting amount is an imm or rcx"
          end in
        let dest = get_value m d in 
        let result = op dest s in 
        store_value result d m;
        rip_incr m;
        let overflow = cond dest s m.flags.fo in
        update_flags m.flags overflow (sign result) (result = Int64.zero)
      | _ -> failwith "handle_shift: More than two operands in this list" in
  
    let handle_data_mov is_push operand_list =
      match operand_list with
      | s::d::[] -> 
        let src = get_value m s in
        store_value src d m;
      | s::[] -> 
        let curr_rsp = m.regs.(rind Rsp) in
        if is_push then 
          let src = get_value m s in
          m.regs.(rind Rsp) <- Int64.sub curr_rsp 8L;
          store_value src (Ind2 Rsp) m;
        else 
          let _val = get_value m (Ind2 Rsp) in
          m.regs.(rind Rsp) <- Int64.add curr_rsp 8L;
          store_value _val s m;
      | _ -> failwith "handle_data_mov: More than two operands in this list" in
  
    match optr, operand_list with
    | Negq, _ -> handle_arith (one_arg_to_two Int64_overflow.neg)
    | Addq, _ -> handle_arith Int64_overflow.add
    | Subq, _ -> handle_arith Int64_overflow.sub
    | Imulq, _ -> handle_arith Int64_overflow.mul
    | Incq, _ -> handle_arith (one_arg_to_two Int64_overflow.succ)
    | Decq, _ -> handle_arith (one_arg_to_two Int64_overflow.pred)
    | Notq, _ -> handle_logic (one_arg_to_two Int64.lognot)
    | Andq, _ -> handle_logic Int64.logand
    | Xorq, _ -> handle_logic Int64.logxor
    | Orq, _ -> handle_logic Int64.logor
    | Sarq, _ -> handle_shift Int64.shift_right (fun dest amt fo -> if amt = 1 then fo else m.flags.fo)
    | Shlq, _ -> handle_shift Int64.shift_left (fun dest amt fo -> 
                    let top_two_bits_diff = (Int64.shift_right_logical dest 62) = 1L || (Int64.shift_right_logical dest 62) = 2L in
                    (amt = 1) && top_two_bits_diff || fo)
    | Shrq, _ -> handle_shift Int64.shift_right_logical (fun dest amt _ -> 
                    if amt = 1 then 
                      (Int64.shift_right_logical dest 63) = 1L 
                    else 
                      m.flags.fo)
    | Movq, _ -> handle_data_mov false operand_list; rip_incr m
    | Leaq, [s; d] -> 
        let v = match s with
          | Imm _ | Reg _ -> failwith "Leaq: Can only be called with Ind"
          | Ind1 i -> get_lit i
          | Ind2 r -> m.regs.(rind r)
          | Ind3 (i, r) -> Int64.add m.regs.(rind r) (get_lit i)
        in store_value v d m; rip_incr m
    | Pushq, _ -> handle_data_mov true operand_list; rip_incr m
    | Popq, _ -> handle_data_mov false operand_list; rip_incr m
    | Cmpq, [s; d] -> 
        let src = get_value m s in
        let dest = get_value m d in
        let res = sub dest src in 
        let fo = res.overflow || (src = Int64.min_int) in
        update_flags m.flags fo (sign res.value) (res.value = Int64.zero); rip_incr m
    | Jmp, [s] -> m.regs.(rind Rip) <- get_value m s
    | Callq, [src] -> 
        handle_data_mov true [Reg Rip];
        m.regs.(rind Rip) <- get_value m src;
    | Retq, _ -> 
        handle_data_mov false [Reg Rip];
        if m.regs.(rind Rip) <> exit_addr then rip_incr m else ()
    | Set s, [src] -> 
        let v = get_value m src in
        let cleared = Int64.logand v (Int64.shift_left Int64.minus_one 8) in
        let new_val = if interp_cnd m.flags s then Int64.logor cleared Int64.one else cleared in
        store_value new_val src m; rip_incr m
    | J j, _ -> 
        if interp_cnd m.flags j then m.regs.(rind Rip) <- get_value m (List.hd operand_list)
        else rip_incr m
    | _, _ -> () in

  let inst = m.mem.(set_addr m.regs.(rind Rip) 0L) in
  begin match inst with
  | InsB0 inst -> execute_ins inst m
  | _ -> ()
  end

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
  let assemble (p:prog) : exec =
    let symbol_table = Hashtbl.create 100 in
    let data_len = function
      | Asciz s -> String.length s + 1
      | Quad  _ -> 8 in
    let add_label lbl n =
      if Hashtbl.mem symbol_table lbl
      then raise (Redefined_sym lbl)
      else Hashtbl.add symbol_table lbl n in
    let text_len e = match e.asm with
      | Text l -> Int64.(mul (of_int (List.length l)) ins_size)
      | Data _ -> 0L in
    let full_text_len = List.fold_left (fun acc e -> Int64.add acc (text_len e)) 0L p in
    let text_pos = ref mem_bot in
    let data_pos = ref (Int64.add mem_bot full_text_len) in
    let elem_update e = match e.asm with
      | Text l -> 
          add_label e.lbl !text_pos;
          text_pos := Int64.(add !text_pos (mul (of_int (List.length l)) ins_size))
      | Data l -> 
          add_label e.lbl !data_pos;
          data_pos := Int64.add !data_pos (Int64.of_int (List.fold_left (+) 0 (List.map data_len l)))
    in
    let patch_imm = function
      | Lit q -> Lit q
      | Lbl l -> 
        if Hashtbl.mem symbol_table l
        then Lit (Hashtbl.find symbol_table l)
        else raise (Undefined_sym l) in
    let patch_op op = match op with
      | Imm i -> Imm (patch_imm i)
      | Ind1 i -> Ind1 (patch_imm i)
      | Ind3 (i, r) -> Ind3 (patch_imm i, r)
      | _ -> op in
    let patch_ins (code, ops) = (code, List.map patch_op ops) in
    let patch_data d = match d with
      | Asciz _ -> d
      | Quad imm -> Quad (patch_imm imm) in
    let patch a = match a with
      | Text l -> Text (List.map patch_ins l)
      | Data l -> Data (List.map patch_data l) in
    let base_exec = 
      List.iter elem_update p;
      { 
        entry = (if Hashtbl.mem symbol_table "main" then Hashtbl.find symbol_table "main" else raise (Undefined_sym "main"));
        text_pos = mem_bot;
        data_pos = Int64.add mem_bot full_text_len;
        text_seg = [];
        data_seg = [];
      } in
    let step a e = match patch a with
      | Text l -> { e with text_seg = (List.concat (List.map sbytes_of_ins l)) @ e.text_seg }
      | Data l -> { e with data_seg = (List.concat (List.map sbytes_of_data l)) @ e.data_seg } in
    List.fold_right step (List.map (fun x -> x.asm) p) base_exec
(*
 Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
  *)
  let load {entry; text_pos; data_pos; text_seg; data_seg} : mach =
    let mem: mem = Array.make mem_size (Byte '\x00') in
    Array.blit (Array.of_list text_seg) 0 mem (Int64.to_int (Int64.sub text_pos mem_bot)) (List.length text_seg);
    Array.blit (Array.of_list data_seg) 0 mem (Int64.to_int (Int64.sub data_pos mem_bot)) (List.length data_seg);
    Array.blit (Array.of_list (sbytes_of_int64 exit_addr)) 0 mem (mem_size - 8) 8;
    { flags = {fo = false; fs = false; fz = false};
      regs = Array.init 17 (fun i -> if i = rind Rip then entry else if i = rind Rsp then Int64.(sub mem_top 8L) else 0L);
      mem }