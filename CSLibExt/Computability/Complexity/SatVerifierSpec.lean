/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.SatTimeM

/-!
# The SAT verifier as `TM2` components: stack formats and specs

`Cslib.CookLevin.satVerifier` decodes the formula `x` (rejecting on failure) and checks every
clause against the witness `w`, read as values of the literal occurrences in order, first
occurrence winning. Its `TM2` machine has three components; this module fixes the stack formats
they share and the pure function each computes, and composes them (`satVerifier_ret_eq`).

* Symbols `Sym`: name bits, polarity markers `lit p`, clause ends `cl`, table markers `val b` and
  `dead`. Names are canonical `encodeNat` strings, so equal names are equal indices.
* Token stack `(toks φ).reverse` (head = top): per literal its name bits then `lit p`, per
  clause a final `cl`, pushed in reading order (names lie reversed under their marker).
* Table stack `tblStk (ents φ w)`: per occurrence its name bits then `val w[i]` (`dead` once `w`
  has run out), pushed alongside the token stack (first occurrence at the bottom).

Components: (1) tokenizer, `tokenize` (the canonical-name check is
`encodeNat_decodeNat_eq_iff`); (2) lookup: from a reversed name block `(q.map .bit).reverse` and
`tblStk es`, compute `liveVal es q` (the last live match scanning from the top) and restore
both stacks; (3) clause check: walk the token stack, looking literals up, giving `checkSpec`.
-/

@[expose] public section

namespace Cslib.Complexity.SatVerifier

open Cslib.CookLevin Cslib.Logic.PL Computability

/-- Symbols of the token and table stacks. -/
inductive Sym
  | bit (b : Bool) | lit (p : Bool) | cl | val (b : Bool) | dead
  deriving DecidableEq

/-- Read a symbol as a name bit; every other symbol ends a name block. -/
def Sym.bit? : Sym → Option Bool
  | .bit b => some b
  | _ => none

/-- Tokens of a literal: its name bits, then its polarity marker. -/
def litToks (l : ℕ × Bool) : List Sym := (encodeNat l.1).map .bit ++ [.lit l.2]

/-- Tokens of a clause: its literals' tokens, then `cl`. -/
def clauseToks (C : CNFClause) : List Sym := C.flatMap litToks ++ [.cl]

/-- Tokens of a formula, in reading order. The token stack holds `(toks φ).reverse`. -/
def toks (φ : CNF) : List Sym := φ.flatMap clauseToks

/-- A table entry: a name and its value, `none` past the end of the witness. -/
abbrev Ent := List Bool × Option Bool

/-- The marker closing a table entry. -/
def markOf : Option Bool → Sym
  | some b => .val b
  | none => .dead

/-- Symbols of a table entry, in reading order. -/
def entToks (e : Ent) : List Sym := e.1.map .bit ++ [markOf e.2]

/-- The table stack of an entry list (head = top; the first entry is at the bottom). -/
def tblStk (es : List Ent) : List Sym := (es.flatMap entToks).reverse

/-- Pair the `i`-th occurrence with `w[i]?`. -/
def entsOf : List ℕ → List Bool → List Ent
  | [], _ => []
  | n :: ns, [] => (encodeNat n, none) :: entsOf ns []
  | n :: ns, b :: bs => (encodeNat n, some b) :: entsOf ns bs

/-- The occurrence table of a formula and a witness. -/
def ents (φ : CNF) (w : List Bool) : List Ent := entsOf (varsOf φ) w

/-- The value of name `q`: the first live entry named `q`, default `false`. -/
def liveVal (es : List Ent) (q : List Bool) : Bool :=
  (es.findSome? fun e => if e.1 = q then e.2 else none).getD false

/-- The clause check: every clause has a literal whose looked-up value is its polarity. -/
def checkSpec (φ : CNF) (es : List Ent) : Bool :=
  φ.all fun C => C.any fun l => liveVal es (encodeNat l.1) == l.2

/-- Component 1: the token stack and the table stack, or `none` (reject). -/
def tokenize (x w : List Bool) : Option (List Sym × List Sym) :=
  (decodeCNF x).map fun φ => ((toks φ).reverse, tblStk (ents φ w))

/-- `encodeNat` is injective. -/
theorem encodeNat_inj {m n : ℕ} : encodeNat m = encodeNat n ↔ m = n :=
  ⟨fun h => by rw [← decode_encodeNat m, h, decode_encodeNat], congrArg _⟩

theorem encodePosNum_decodePosNum_eq_iff (l : List Bool) :
    encodePosNum (decodePosNum l) = l ↔ l.getLast? = some true := by
  induction l with
  | nil => simp [decodePosNum, encodePosNum]
  | cons b l ih =>
      cases l with
      | nil => cases b <;> simp [decodePosNum, encodePosNum]
      | cons c l =>
          cases b <;> simpa [decodePosNum, encodePosNum, List.getLast?_cons_cons] using ih

/-- Canonical names: a bit string is some `encodeNat n` iff it is empty or ends in `true`. -/
theorem encodeNat_decodeNat_eq_iff (l : List Bool) :
    encodeNat (decodeNat l) = l ↔ l = [] ∨ l.getLast? = some true := by
  have h : encodeNat (decodeNat l) = encodeNum (decodeNum l) := by
    simp only [encodeNat, decodeNat, Num.of_to_nat]
  rw [h]
  by_cases hl : l = []
  · subst hl; simp [decodeNum, encodeNum]
  · simp only [decodeNum, hl, ite_false, false_or]
    rw [PosNum.cast_to_num]
    exact encodePosNum_decodePosNum_eq_iff l

theorem liveVal_entsOf_nil (ns : List ℕ) (q : List Bool) : liveVal (entsOf ns []) q = false := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simpa [liveVal, entsOf, List.findSome?_cons] using ih

/-- The occurrence table answers lookups exactly as `lookupVar`. -/
theorem liveVal_entsOf (ns : List ℕ) (w : List Bool) (x : ℕ) :
    liveVal (entsOf ns w) (encodeNat x) = (lookupVar ns w x).ret := by
  induction ns generalizing w with
  | nil => simp [entsOf, liveVal, lookupVar]
  | cons n ns ih =>
      cases w with
      | nil =>
          rw [liveVal_entsOf_nil]
          simp [lookupVar]
      | cons b bs =>
          by_cases h : x = n
          · subst h; simp [entsOf, liveVal, lookupVar]
          · have h' : ¬ encodeNat n = encodeNat x := fun e => h (encodeNat_inj.1 e).symm
            simpa [entsOf, liveVal, lookupVar, h, h'] using ih bs

/-- Component 3's spec on the occurrence table is `checkCNF`. -/
theorem checkSpec_ents (φ : CNF) (w : List Bool) :
    checkSpec φ (ents φ w) = (checkCNF (varsOf φ) w φ).ret := by
  rw [Bool.eq_iff_iff, checkCNF_ret, CNF.satisfies_def]
  simp [checkSpec, ents, liveVal_entsOf]

/-- The components compose to `satVerifier`. -/
theorem satVerifier_ret_eq (x w : List Bool) :
    (satVerifier (x, w)).ret = ((decodeCNF x).map fun φ => checkSpec φ (ents φ w)).getD false := by
  cases h : decodeCNF x with
  | none => simp [satVerifier_none h]
  | some φ => simp [satVerifier_some h, checkSpec_ents]

/-- `Sym` is finite. -/
instance Sym.instFintype : Fintype Sym where
  elems := ⟨↑[Sym.bit false, .bit true, .lit false, .lit true, .cl, .val false, .val true, .dead],
    by decide⟩
  complete := fun x => by rcases x with b | b | _ | b | _ <;> (try cases b) <;> decide

/-- A clause has no more tokens than encoding bits. -/
theorem clauseToks_length_le (C : CNFClause) :
    (clauseToks C).length ≤ (encodeClause C).length := by
  simp only [clauseToks, encodeClause, List.length_append, List.length_flatMap, List.length_cons,
    List.length_replicate, List.length_nil, litToks, encodeLit, encodeNatPrefix,
    MetaMathlibExt.BitstringEncoding.length_delimit, List.length_map]
  induction C with
  | nil => simp
  | cons l C ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

/-- The token stack is no longer than the encoding. -/
theorem toks_length_le (φ : CNF) : (toks φ).length ≤ (encodeCNF φ).length := by
  simp only [toks, encodeCNF, List.length_append, List.length_cons, List.length_replicate,
    List.length_flatMap]
  induction φ with
  | nil => simp
  | cons C φ ih =>
      have := clauseToks_length_le C
      simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

end Cslib.Complexity.SatVerifier
