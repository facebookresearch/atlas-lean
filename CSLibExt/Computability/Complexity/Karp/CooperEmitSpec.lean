/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Cooper
public import CSLibExt.Computability.Complexity.SatCheck

@[expose] public section

/-!
# Cooper's network, emitted from the SAT token stack

The emission that writes the code of Cooper's network (Cooper 1990, Section 4) from the SAT
token stack `(toks φ).reverse`, head = top: the clauses from the last one, each a clause marker
`cl` followed by its literals from the last one, each literal a polarity marker `lit p` followed
by its name bits from the most significant one. The output is a stack read top first, so a node
is written by prepending its code: node `0` (constant true) before the first token; per clause a
constant-false node, per literal a root node at the first occurrence of its variable and then an
OR node, and at the end of the clause an AND node; at the end of the stack the node count, in
unary. This is the order and the node numbering of `Cslib.Complexity.Cooper.coopSt`. The root of
a repeated variable is found by its name, an `encodeNat` string, so equal names are equal
variables.

The emission has two layers: `stepTok`, `walkTok` and `emitTok` read single tokens, and `eLit`,
`eClause` and `eFormula` add whole literals, clauses and formulas, the blocks a machine handles.
`walkTok_toks` ties the token layer to the block layer and `eFormula_eq` the block layer to the
construction; `emitTok_toks` gives the code of Cooper's network on every formula, and
`outBN_eq_reduceBN` gives the emission on bit strings equal to the reduction map `reduceBN` on
every input. Undecodable input goes to the code of the fixed no-instance `noBN`, the output an
emitter reserves for it in `Cslib.Complexity.Karp.TokThen.out`. The last section records facts a
machine implementation uses: the layout of a gate node's code, a bound on the node count, and
bounds on the counters and the dictionary.

Reference: G. F. Cooper, "The computational complexity of probabilistic inference using Bayesian
belief networks", Artificial Intelligence 42 (1990), 393-405.
-/

namespace Cslib.Complexity.Karp.EmitCooper

open Cslib.CookLevin Cslib.Logic.LegacyPL Computability Cslib.Complexity.SatVerifier
  Cslib.Complexity.Cooper

/-! ### Emitter state and block emission, in walk order -/

/-- **Emitter state between token blocks.** The output written so far, the node counter, the
AND-chain output, the chain output of the open clause and the dictionary of roots. A name is a
variable's `encodeNat` string, least significant bit first. -/
structure ESt where
  /-- The output stack, top first: the codes of the nodes written so far, newest first. -/
  out : List Bool
  /-- The node counter: the index of the next node. -/
  n : ℕ
  /-- The output node of the AND chain. -/
  acc : ℕ
  /-- The output node of the open clause's OR chain; `0` between clauses. -/
  o : ℕ
  /-- Pairs (name, root node) for the variables met so far, latest first. -/
  dict : List (List Bool × ℕ)

/-- **Writing a node.** Prepend the node's code to the output and advance the node counter. -/
def ESt.push (v : RatNode) (s : ESt) : ESt :=
  { s with out := encodeRatNode v ++ s.out, n := s.n + 1 }

/-- **Initial state.** Node `0`, the constant-true node, is written: the node counter is `1`,
the AND-chain output and the chain output are node `0`, and the dictionary is empty. -/
def eInit : ESt := ⟨encodeRatNode (constNode true), 1, 0, 0, []⟩

/-- **Root of a name.** The root recorded under the name, or a root node written now and recorded
under the name; returned with the state. -/
def eRoot (nm : List Bool) (s : ESt) : ESt × ℕ :=
  match s.dict.lookup nm with
  | some v => (s, v)
  | none => ({ s.push rootNode with dict := (nm, s.n) :: s.dict }, s.n)

/-- **Adding a literal.** For a literal of polarity `p` whose variable has the name `nm`: the root
of the name (written at its first occurrence), then an OR node joining the open clause's chain
output to the root. The OR node is the new chain output. -/
def eLit (p : Bool) (nm : List Bool) (s : ESt) : ESt :=
  let r := eRoot nm s
  { r.1.push (orNode s.o r.2 p) with o := r.1.n }

/-- **Opening a clause.** Write a constant-false node, the open clause's chain output. -/
def eOpen (s : ESt) : ESt := { s.push (constNode false) with o := s.n }

/-- **Closing a clause.** Write an AND node joining the AND chain to the clause's chain output; it
becomes the AND-chain output, and the chain output is reset to `0`. -/
def eClose (s : ESt) : ESt := { s.push (andNode s.acc s.o) with acc := s.n, o := 0 }

/-- **Adding a clause.** Open the clause, add its literals from the last one, then close it: the
order in which the token stack presents a clause. -/
def eClause (C : CNFClause) (s : ESt) : ESt :=
  eClose (C.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen s))

/-- **The block emission of a formula.** From the initial state, add the clauses from the last
one, the order in which the token stack presents them. -/
def eFormula (φ : CNF) : ESt := φ.reverse.foldl (fun s C => eClause C s) eInit

/-! ### The emission over the SAT token stack -/

/-- **Reading position** between tokens: no clause open yet, inside a clause, or after the
polarity marker `lit p` of a literal with the name bits read so far. -/
inductive Pos
  /-- No clause is open: before the first token. -/
  | top
  /-- Inside a clause, with no literal pending. -/
  | cls
  /-- After the marker `lit p`; `nm` holds the name bits read so far, the latest at the head. -/
  | name (p : Bool) (nm : List Bool)

/-- **End of the stack.** Add the pending literal, if any, and close the open clause, if any. -/
def finishTok : Pos × ESt → ESt
  | (.top, s) => s
  | (.cls, s) => eClose s
  | (.name p nm, s) => eClose (eLit p nm s)

/-- **Reading one token.** A clause marker `cl` first finishes what is open, as at the end of the
stack, then opens a clause. A polarity marker `lit q` inside a clause adds the pending literal,
if any, and starts a literal of polarity `q`. A name bit after a polarity marker is prepended to
the pending name. Any other combination of position and token leaves the state unchanged. -/
def stepTok : Pos × ESt → Sym → Pos × ESt
  | x, .cl => (.cls, eOpen (finishTok x))
  | (.cls, s), .lit p => (.name p [], s)
  | (.name p nm, s), .lit q => (.name q [], eLit p nm s)
  | (.name p nm, s), .bit b => (.name p (b :: nm), s)
  | x, _ => x

/-- **Walking a token stack.** Read the tokens from the head, from the initial state, then
finish. -/
def walkTok (ts : List Sym) : ESt := finishTok (ts.foldl stepTok (.top, eInit))

/-- **The emission on a token stack**: the node count in unary, then the codes of the nodes,
newest first; the output stack once the count is pushed last. -/
def emitTok (ts : List Sym) : List Bool := unary (walkTok ts).n ++ (walkTok ts).out

/-- **The emission on bit strings.** A bit string that decodes to a CNF formula `φ` goes to the
emission on its token stack `(toks φ).reverse`; any other bit string goes to the code of the
fixed no-instance `noBN`, the output a tokenize-then-emit machine writes for undecodable input
(`Cslib.Complexity.Karp.TokThen.out`). -/
def outBN (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => emitTok (toks φ).reverse
  | none => encodeRatNet noBN

/-- **A construction state as an emitter state**, with chain output `o`: the codes of the nodes
from the last to the first, the node count, the AND-chain output, and the root of each recorded
variable under the variable's `encodeNat` name. -/
def ofCoop (s : CoopSt) (o : ℕ) : ESt :=
  ⟨s.nodes.reverse.flatMap encodeRatNode, s.nodes.length, s.acc, o,
    s.roots.map fun r => (encodeNat r.1, r.2)⟩

/-- **Adding the pending literal**, if any. -/
def flushLit : Pos × ESt → ESt
  | (.name p nm, s) => eLit p nm s
  | (_, s) => s

/-! ### Equalities -/

/-- **Names as keys.** Looking up the `encodeNat` name of `x` among the names of a list of pairs
(variable, root) finds what looking up `x` itself finds. -/
theorem lookup_names (x : ℕ) (roots : List (ℕ × ℕ)) :
    (roots.map fun r => (encodeNat r.1, r.2)).lookup (encodeNat x) = roots.lookup x := by
  induction roots with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.lookup]
    by_cases h : r.1 = x
    · subst h
      simp
    · have e1 : (x == r.1) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      have e2 : (encodeNat x == encodeNat r.1) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro he
        apply h
        have hdec := congrArg Computability.decodeNat he
        rw [Computability.decode_encodeNat, Computability.decode_encodeNat] at hdec
        exact hdec.symm
      rw [e1, e2]
      exact ih

/-- **A literal, against the construction.** Adding a literal to the emitter state of a
construction state gives the emitter state of `coopLit`, with its OR node as chain output. -/
theorem eLit_ofCoop (l : ℕ × Bool) (o : ℕ) (s : CoopSt) :
    eLit l.2 (encodeNat l.1) (ofCoop s o) = ofCoop (coopLit l o s).1 (coopLit l o s).2 := by
  simp only [eLit, eRoot, coopLit, coopRoot, ofCoop]
  rw [lookup_names]
  cases List.lookup l.1 s.roots <;> simp [ESt.push]

private theorem emit_aux_coopLit_acc (l : ℕ × Bool) (o : ℕ) (s : CoopSt) :
    (coopLit l o s).1.acc = s.acc := by
  cases h : List.lookup l.1 s.roots <;> simp [coopLit, coopRoot, h]

private theorem emit_aux_coopLits_acc (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt) :
    (coopLits ls o s).1.acc = s.acc := by
  induction ls generalizing o s with
  | nil => rfl
  | cons l ls ih => simp only [coopLits, ih, emit_aux_coopLit_acc]

private theorem emit_aux_eOpen_ofCoop (s : CoopSt) (o : ℕ) :
    eOpen (ofCoop s o) =
      ofCoop { s with nodes := s.nodes ++ [constNode false] } s.nodes.length := by
  simp [eOpen, ofCoop, ESt.push]

private theorem emit_aux_foldl_eLit (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt) :
    ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (ofCoop s o) =
      ofCoop (coopLits ls o s).1 (coopLits ls o s).2 := by
  induction ls generalizing o s with
  | nil => rfl
  | cons l ls ih => simp only [List.foldl_cons, eLit_ofCoop, ih, coopLits]

/-- **A clause, against the construction.** Adding a clause to the emitter state of a
construction state, with any chain output, gives the emitter state of `coopClause` with chain
output `0`. -/
theorem eClause_ofCoop (C : CNFClause) (s : CoopSt) (o : ℕ) :
    eClause C (ofCoop s o) = ofCoop (coopClause C s) 0 := by
  simp only [eClause, coopClause, emit_aux_eOpen_ofCoop, emit_aux_foldl_eLit]
  simp [eClose, ofCoop, ESt.push, emit_aux_coopLits_acc]

private theorem emit_aux_eInit : eInit = ofCoop ⟨[constNode true], [], 0⟩ 0 := by
  simp [eInit, ofCoop]

private theorem emit_aux_foldl_eClause (l : List CNFClause) (s : CoopSt) :
    l.foldl (fun s C => eClause C s) (ofCoop s 0) =
      ofCoop (l.foldl (fun s C => coopClause C s) s) 0 := by
  induction l generalizing s with
  | nil => rfl
  | cons C l ih => simp only [List.foldl_cons, eClause_ofCoop, ih]

/-- **The block emission is the construction**: it ends in the emitter state of `coopSt φ`. -/
theorem eFormula_eq (φ : CNF) : eFormula φ = ofCoop (coopSt φ) 0 := by
  simp only [eFormula, coopSt, emit_aux_eInit, emit_aux_foldl_eClause]

/-- **A clause marker** finishes what is open, then opens a clause. -/
theorem stepTok_cl (x : Pos × ESt) : stepTok x .cl = (.cls, eOpen (finishTok x)) := by
  obtain ⟨p, s⟩ := x
  cases p <;> rfl

private theorem emit_aux_foldl_bits (bs nm : List Bool) (p : Bool) (s : ESt) :
    (((bs.map Sym.bit).reverse).foldl stepTok (.name p nm, s)) =
      (.name p (bs ++ nm), s) := by
  induction bs generalizing nm with
  | nil => rfl
  | cons b bs ih =>
    rw [List.map_cons, List.reverse_cons, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih]
    rfl

/-- **A literal's tokens.** Once a clause is open, reading the stack tokens of a literal (its
polarity marker, then its name bits from the most significant one) adds the pending literal, if
any, and leaves the literal pending under its full `encodeNat` name. -/
theorem foldl_litRev (l : ℕ × Bool) (x : Pos × ESt) (hx : x.1 ≠ .top) :
    (Check.litRev l).foldl stepTok x = (.name l.2 (encodeNat l.1), flushLit x) := by
  obtain ⟨px, s⟩ := x
  cases px with
  | top => exact absurd rfl hx
  | cls =>
    simp only [Check.litRev, List.foldl_cons]
    rw [show stepTok (Pos.cls, s) (.lit l.2) = (Pos.name l.2 [], s) from rfl]
    rw [emit_aux_foldl_bits, List.append_nil]
    rfl
  | name p nm =>
    simp only [Check.litRev, List.foldl_cons]
    rw [show stepTok (Pos.name p nm, s) (.lit l.2) =
      (Pos.name l.2 [], eLit p nm s) from rfl]
    rw [emit_aux_foldl_bits, List.append_nil]
    rfl

private theorem emit_aux_finishTok_flatMap_name (ls : List (ℕ × Bool)) (p : Bool)
    (nm : List Bool) (s : ESt) :
    finishTok ((ls.flatMap Check.litRev).foldl stepTok (.name p nm, s)) =
      eClose (ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eLit p nm s)) := by
  induction ls generalizing p nm s with
  | nil => rfl
  | cons l ls ih =>
    rw [List.flatMap_cons, List.foldl_append, foldl_litRev _ _ (by simp), List.foldl_cons]
    exact ih _ _ _

private theorem emit_aux_finishTok_flatMap_cls (ls : List (ℕ × Bool)) (s : ESt) :
    finishTok ((ls.flatMap Check.litRev).foldl stepTok (.cls, s)) =
      eClose (ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) s) := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih =>
    rw [List.flatMap_cons, List.foldl_append, foldl_litRev _ _ (by simp), List.foldl_cons]
    exact emit_aux_finishTok_flatMap_name _ _ _ _

/-- **A clause's tokens.** Reading the stack tokens of a clause (its marker, then its literals
from the last one) and finishing adds the clause to what finishing gives before them. -/
theorem finishTok_clRev (C : CNFClause) (x : Pos × ESt) :
    finishTok ((Check.clRev C).foldl stepTok x) = eClause C (finishTok x) := by
  simp only [Check.clRev, List.foldl_cons, stepTok_cl, emit_aux_finishTok_flatMap_cls,
    eClause]

private theorem emit_aux_walkTok_flatMap (l : List CNFClause) (x : Pos × ESt) :
    finishTok ((l.flatMap Check.clRev).foldl stepTok x) =
      l.foldl (fun s C => eClause C s) (finishTok x) := by
  induction l generalizing x with
  | nil => rfl
  | cons C l ih =>
    rw [List.flatMap_cons, List.foldl_append, ih, finishTok_clRev, List.foldl_cons]

/-- **The token walk is the block emission**: on the token stack of a formula, walking the
tokens ends in the state of the block emission. -/
theorem walkTok_toks (φ : CNF) : walkTok (toks φ).reverse = eFormula φ := by
  unfold walkTok eFormula
  rw [Check.toks_reverse, emit_aux_walkTok_flatMap]
  rfl

/-- **The emission writes Cooper's network.** On the token stack of a CNF formula `φ`, the
emission is the code of `cooperNet φ`. -/
theorem emitTok_toks (φ : CNF) :
    emitTok (toks φ).reverse = encodeRatNet (cooperNet φ) := by
  unfold emitTok
  rw [walkTok_toks, eFormula_eq]
  rfl

/-- **The emission is the encoded reduction.** On every bit string, the emission equals Cooper's
reduction map `reduceBN`, undecodable input included. -/
theorem outBN_eq_reduceBN (x : List Bool) : outBN x = reduceBN x := by
  unfold outBN reduceBN
  cases decodeCNF x with
  | none => rfl
  | some φ => exact emitTok_toks φ

/-! ### Facts for a machine implementation -/

/-- **Rows of a gate node's code**: the codes of the four rows of the table of the gate `f`;
the rows do not mention the parents. -/
def gateRows (f : Bool → Bool → Bool) : List Bool := (gateNode f 0 0).2.flatMap encodeRow

/-- **Layout of a gate node's code**: the parent count `2`, the parents `i` and `j`, the row
count `4`, all in unary, then the rows. -/
theorem encodeRatNode_gateNode (f : Bool → Bool → Bool) (i j : ℕ) :
    encodeRatNode (gateNode f i j) = unary 2 ++ unary i ++ unary j ++ unary 4 ++ gateRows f := by
  simp [encodeRatNode, gateNode, gateRows]

private theorem emit_aux_eRoot_n_le (nm : List Bool) (s : ESt) :
    (eRoot nm s).1.n ≤ s.n + 1 := by
  unfold eRoot
  split <;> simp [ESt.push]

private theorem emit_aux_eLit_n_le (p : Bool) (nm : List Bool) (s : ESt) :
    (eLit p nm s).n ≤ s.n + 2 := by
  have h := emit_aux_eRoot_n_le nm s
  simp only [eLit, ESt.push] at ⊢
  omega

private theorem emit_aux_foldl_eLit_n_le (ls : List (ℕ × Bool)) (s : ESt) :
    (ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) s).n ≤ s.n + 2 * ls.length := by
  induction ls generalizing s with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := emit_aux_eLit_n_le l.2 (encodeNat l.1) s
    have h2 := ih (eLit l.2 (encodeNat l.1) s)
    omega

private theorem emit_aux_eClause_n_le (C : CNFClause) (s : ESt) :
    (eClause C s).n ≤ s.n + 2 + 2 * C.length := by
  have hOpen : (eOpen s).n = s.n + 1 := by simp [eOpen, ESt.push]
  have hFold := emit_aux_foldl_eLit_n_le C.reverse (eOpen s)
  rw [hOpen, List.length_reverse] at hFold
  have hClose : (eClause C s).n =
      (C.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen s)).n + 1 := by
    simp [eClause, eClose, ESt.push]
  omega

private theorem emit_aux_litToks_length_pos (l : ℕ × Bool) :
    1 ≤ (litToks l).length := by
  have heq : (litToks l).length = (encodeNat l.1).length + 1 := by simp [litToks]
  omega

private theorem emit_aux_flatMap_litToks_length_ge (ls : List (ℕ × Bool)) :
    ls.length ≤ (ls.flatMap litToks).length := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h := emit_aux_litToks_length_pos l
    omega

private theorem emit_aux_clauseToks_length_ge (C : CNFClause) :
    C.length + 1 ≤ (clauseToks C).length := by
  have h := emit_aux_flatMap_litToks_length_ge C
  have heq : (clauseToks C).length = (C.flatMap litToks).length + 1 := by
    simp [clauseToks]
  omega

private theorem emit_aux_reverse_flatMap_length (l : List CNFClause) :
    (l.reverse.flatMap clauseToks).length = (l.flatMap clauseToks).length := by
  induction l with
  | nil => simp
  | cons C l ih =>
    simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.length_append] at ih ⊢
    omega

private theorem emit_aux_foldl_eClause_n_le (l : List CNFClause) (s : ESt) :
    (l.foldl (fun s C => eClause C s) s).n ≤ s.n + 2 * (l.flatMap clauseToks).length := by
  induction l generalizing s with
  | nil => simp
  | cons C l ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.length_append]
    have hC := emit_aux_eClause_n_le C s
    have hCl := emit_aux_clauseToks_length_ge C
    have h2 := ih (eClause C s)
    omega

/-- **Node count.** The block emission of `φ` writes at most `2 |toks φ| + 1` nodes. -/
theorem eFormula_n_le (φ : CNF) : (eFormula φ).n ≤ 2 * (toks φ).length + 1 := by
  unfold eFormula toks
  have h := emit_aux_foldl_eClause_n_le φ.reverse eInit
  have hInit : eInit.n = 1 := rfl
  have hRev := emit_aux_reverse_flatMap_length φ
  omega

/-- **Counters in range**: the AND-chain output, the chain output and every recorded root lie
below the node counter. -/
def ESt.Inv (s : ESt) : Prop := s.acc < s.n ∧ s.o < s.n ∧ ∀ e ∈ s.dict, e.2 < s.n

/-- **Counters in range after a formula.** The block emission of a formula ends with its counters
in range. -/
theorem eFormula_inv (φ : CNF) : (eFormula φ).Inv := by
  have hg := good_coopSt φ
  have hacc := hg.acc_lt
  rw [eFormula_eq]
  simp only [ESt.Inv, ofCoop]
  refine ⟨hacc, by omega, ?_⟩
  intro e he
  rw [List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  exact (hg.roots_ok p hp).1

private theorem emit_aux_eRoot_dict_le (nm : List Bool) (s : ESt) :
    (eRoot nm s).1.dict.length ≤ s.dict.length + 1 := by
  unfold eRoot
  split <;> simp

private theorem emit_aux_eLit_dict_le (p : Bool) (nm : List Bool) (s : ESt) :
    (eLit p nm s).dict.length ≤ s.dict.length + 1 := by
  have h := emit_aux_eRoot_dict_le nm s
  simp only [eLit, ESt.push] at ⊢
  omega

private theorem emit_aux_foldl_eLit_dict_le (ls : List (ℕ × Bool)) (s : ESt) :
    (ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) s).dict.length ≤
      s.dict.length + ls.length := by
  induction ls generalizing s with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := emit_aux_eLit_dict_le l.2 (encodeNat l.1) s
    have h2 := ih (eLit l.2 (encodeNat l.1) s)
    omega

private theorem emit_aux_eClause_dict_le (C : CNFClause) (s : ESt) :
    (eClause C s).dict.length ≤ s.dict.length + C.length := by
  have hOpen : (eOpen s).dict = s.dict := by simp [eOpen, ESt.push]
  have hFold := emit_aux_foldl_eLit_dict_le C.reverse (eOpen s)
  rw [hOpen, List.length_reverse] at hFold
  have hClose : (eClause C s).dict.length =
      (C.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen s)).dict.length := by
    simp [eClause, eClose, ESt.push]
  omega

private theorem emit_aux_foldl_eClause_dict_le (l : List CNFClause) (s : ESt) :
    (l.foldl (fun s C => eClause C s) s).dict.length ≤
      s.dict.length + (l.flatMap clauseToks).length := by
  induction l generalizing s with
  | nil => simp
  | cons C l ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.length_append]
    have hC := emit_aux_eClause_dict_le C s
    have hCl := emit_aux_clauseToks_length_ge C
    have h2 := ih (eClause C s)
    omega

private theorem emit_aux_eRoot_dict_mem (nm : List Bool) (s : ESt) (e : List Bool × ℕ)
    (he : e ∈ (eRoot nm s).1.dict) : e ∈ s.dict ∨ e.1 = nm := by
  cases h : s.dict.lookup nm with
  | some v =>
    have hEq : (eRoot nm s).1 = s := by simp [eRoot, h]
    rw [hEq] at he
    exact Or.inl he
  | none =>
    have hEq : (eRoot nm s).1.dict = (nm, s.n) :: s.dict := by simp [eRoot, h, ESt.push]
    rw [hEq, List.mem_cons] at he
    cases he with
    | inl heq => subst heq; exact Or.inr rfl
    | inr hm => exact Or.inl hm

private theorem emit_aux_eLit_dict_mem (p : Bool) (nm : List Bool) (s : ESt)
    (e : List Bool × ℕ) (he : e ∈ (eLit p nm s).dict) : e ∈ s.dict ∨ e.1 = nm := by
  have he' : e ∈ (eRoot nm s).1.dict := by simpa [eLit, ESt.push] using he
  exact emit_aux_eRoot_dict_mem nm s e he'

private theorem emit_aux_foldl_eLit_dict_mem (ls : List (ℕ × Bool)) (s : ESt)
    (e : List Bool × ℕ) :
    e ∈ (ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) s).dict →
    e ∈ s.dict ∨ ∃ l ∈ ls, e.1 = encodeNat l.1 := by
  induction ls generalizing s with
  | nil => intro he; simp only [List.foldl_nil] at he; exact Or.inl he
  | cons l ls ih =>
    intro he
    simp only [List.foldl_cons] at he
    have h := ih _ he
    cases h with
    | inl hm =>
      have h2 := emit_aux_eLit_dict_mem l.2 (encodeNat l.1) s e hm
      cases h2 with
      | inl hm2 => exact Or.inl hm2
      | inr hnm =>
        exact Or.inr ⟨l, by rw [List.mem_cons]; exact Or.inl rfl, hnm⟩
    | inr hex =>
      obtain ⟨m, hm, hnm⟩ := hex
      exact Or.inr ⟨m, by rw [List.mem_cons]; exact Or.inr hm, hnm⟩

private theorem emit_aux_eClause_dict_mem (C : CNFClause) (s : ESt) (e : List Bool × ℕ)
    (he : e ∈ (eClause C s).dict) :
    e ∈ s.dict ∨ ∃ l ∈ C, e.1 = encodeNat l.1 := by
  have he' : e ∈ (C.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen s)).dict := by
    simpa [eClause, eClose, ESt.push] using he
  have h := emit_aux_foldl_eLit_dict_mem C.reverse (eOpen s) e he'
  have hOpen : (eOpen s).dict = s.dict := by simp [eOpen, ESt.push]
  cases h with
  | inl hm => rw [hOpen] at hm; exact Or.inl hm
  | inr hex =>
    obtain ⟨l, hl, hnm⟩ := hex
    rw [List.mem_reverse] at hl
    exact Or.inr ⟨l, hl, hnm⟩

private theorem emit_aux_foldl_eClause_dict_mem (l : List CNFClause) (s : ESt)
    (e : List Bool × ℕ) :
    e ∈ (l.foldl (fun s C => eClause C s) s).dict →
    e ∈ s.dict ∨ ∃ C ∈ l, ∃ m ∈ C, e.1 = encodeNat m.1 := by
  induction l generalizing s with
  | nil => intro he; simp only [List.foldl_nil] at he; exact Or.inl he
  | cons C l ih =>
    intro he
    simp only [List.foldl_cons] at he
    have h := ih _ he
    cases h with
    | inl hm =>
      have h2 := emit_aux_eClause_dict_mem C s e hm
      cases h2 with
      | inl hm2 => exact Or.inl hm2
      | inr hex =>
        obtain ⟨m, hm, hnm⟩ := hex
        exact Or.inr ⟨C, by rw [List.mem_cons]; exact Or.inl rfl, m, hm, hnm⟩
    | inr hex =>
      obtain ⟨C', hC', m, hm, hnm⟩ := hex
      exact Or.inr ⟨C', by rw [List.mem_cons]; exact Or.inr hC', m, hm, hnm⟩

private theorem emit_aux_mem_flatMap_length_le {α β : Type} (a : α) (ls : List α)
    (f : α → List β) : a ∈ ls → (f a).length ≤ (ls.flatMap f).length := by
  induction ls with
  | nil => intro h; simp at h
  | cons hd tl ih =>
    intro h
    simp only [List.flatMap_cons, List.length_append]
    rw [List.mem_cons] at h
    cases h with
    | inl heq => subst heq; exact Nat.le_add_right _ _
    | inr hm => exact Nat.le_trans (ih hm) (Nat.le_add_left _ _)

private theorem emit_aux_encodeNat_length_le_toks (l : ℕ × Bool) (C : CNFClause) (φ : CNF)
    (hl : l ∈ C) (hC : C ∈ φ) : (encodeNat l.1).length ≤ (toks φ).length := by
  have h1 : (litToks l).length = (encodeNat l.1).length + 1 := by simp [litToks]
  have h2 : (litToks l).length ≤ (C.flatMap litToks).length :=
    emit_aux_mem_flatMap_length_le l C litToks hl
  have h3 : (clauseToks C).length = (C.flatMap litToks).length + 1 := by simp [clauseToks]
  have h4 : (clauseToks C).length ≤ (toks φ).length := by
    simp only [toks]
    exact emit_aux_mem_flatMap_length_le C φ clauseToks hC
  omega

/-- **Dictionary size.** After the block emission of `φ` the dictionary has at most `|toks φ|`
entries, and every name in it has at most `|toks φ|` bits. -/
theorem eFormula_dict_le (φ : CNF) : (eFormula φ).dict.length ≤ (toks φ).length ∧
    ∀ e ∈ (eFormula φ).dict, e.1.length ≤ (toks φ).length := by
  constructor
  · unfold eFormula toks
    have h := emit_aux_foldl_eClause_dict_le φ.reverse eInit
    have hInit : eInit.dict.length = 0 := rfl
    have hRev := emit_aux_reverse_flatMap_length φ
    omega
  · intro e he
    simp only [eFormula] at he
    have hInit : eInit.dict = [] := rfl
    have hmem := emit_aux_foldl_eClause_dict_mem φ.reverse eInit e he
    rw [hInit, List.mem_nil_iff] at hmem
    obtain ⟨C, hC, m, hm, hnm⟩ := hmem.resolve_left (by simp)
    rw [List.mem_reverse] at hC
    rw [hnm]
    exact emit_aux_encodeNat_length_le_toks m C φ hm hC

end Cslib.Complexity.Karp.EmitCooper
