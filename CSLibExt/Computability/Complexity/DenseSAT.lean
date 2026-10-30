/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `CookLevin.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/CookLevin.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.DenseSAT` namespace, `SAT` stated as a `List Bool → Prop` predicate instead of
the source repository's `Language` type, the verifier machine moved to its own module, and the
sanity examples moved to `CSLibExtTest`.
-/

module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# Dense CNF-SAT

A concrete CNF-SAT language over bit strings, `Cslib.Complexity.DenseSAT.SAT`, with the
"dense" clause encoding of `JoshuaTan42/millennium-cook-levin`, its semantics, sanity checks,
and the certificate check `check` used by the polynomial-time verifier machine
(`CSLibExt.Computability.Complexity.DenseSATVerifier`).

Encoding: a CNF is a list of *dense* clauses; a clause is a list of slots `Option Bool`
(`none` = variable absent, `some b` = literal `x_j = b`, where `j` is the slot position).
Bits are read in pairs: `00` ends a clause, `01` absent, `10` positive, `11` negative. Decoding
is total: a trailing unterminated clause and a dangling odd bit are ignored, so strings with no
`00` decode to the empty (satisfiable) formula.

This is not the binary-index encoding of `Cslib.CookLevin.encodeCNF`
(`CSLibExt/Computability/CookLevin.lean`), on which `Cslib.CookLevin.satDec` and the
`theorem_wanted` Cook-Levin statement are phrased. The dense encoding writes variable `x_j`
as slot `j` of every clause that mentions it, so the two encodings are polynomially related
only after renumbering variables; relating them needs an encoding-converter machine.
-/

@[expose] public section

namespace Cslib.Complexity.DenseSAT


/-- A clause as a dense row: slot `j` says how variable `x_j` occurs
(`none`: absent, `some true`: `x_j`, `some false`: `¬x_j`). -/
abbrev Clause := List (Option Bool)

/-- A CNF formula: the conjunction of its clauses. -/
abbrev CNF := List Clause

/-- `a` satisfies clause `c`: some slot `j` holds a literal `x_j = b` and `a[j] = b`.
Variables at indices `≥ a.length` are unassigned and satisfy no literal. -/
def clauseSat (c : Clause) (a : List Bool) : Prop :=
  ∃ (j : ℕ) (b : Bool), c[j]? = some (some b) ∧ a[j]? = some b

/-- `a` satisfies every clause of `φ`. -/
def cnfSat (φ : CNF) (a : List Bool) : Prop :=
  ∀ c ∈ φ, clauseSat c a

/-- Decoding with the current (reversed) unfinished clause as accumulator. A trailing unterminated
clause and a dangling odd bit are ignored, so decoding is total. -/
def decodeAux : List Bool → Clause → CNF
  | false :: false :: r, cur => cur.reverse :: decodeAux r []
  | false :: true :: r, cur => decodeAux r (none :: cur)
  | true :: s :: r, cur => decodeAux r (some (!s) :: cur)
  | _, _ => []

/-- Decode a bit string into a CNF formula. -/
def decodeCNF (w : List Bool) : CNF := decodeAux w []

/-- Two bits per slot: `none ↦ 01`, `some true ↦ 10`, `some false ↦ 11`. -/
def encodeSlot : Option Bool → List Bool
  | none => [false, true]
  | some b => [true, !b]

/-- A clause is its slots followed by the terminator `00`. -/
def encodeClause (c : Clause) : List Bool := c.flatMap encodeSlot ++ [false, false]

/-- Encode a CNF formula as a bit string. -/
def encodeCNF (φ : CNF) : List Bool := φ.flatMap encodeClause

theorem decodeAux_slots (c : Clause) (rest : List Bool) (cur : Clause) :
    decodeAux (c.flatMap encodeSlot ++ rest) cur = decodeAux rest (c.reverse ++ cur) := by
  induction c generalizing cur with
  | nil => rfl
  | cons x c ih =>
      cases x with
      | none => simp [encodeSlot, decodeAux, ih]
      | some b => simp [encodeSlot, decodeAux, ih]

/-- Sanity: every CNF is represented, and decodes back to itself. -/
theorem decodeCNF_encodeCNF (φ : CNF) : decodeCNF (encodeCNF φ) = φ := by
  unfold decodeCNF encodeCNF
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [List.flatMap_cons, encodeClause, List.append_assoc, decodeAux_slots]
      simp [decodeAux, ih]

/-- **CNF-SAT** over binary strings: the decoded formula has a satisfying assignment. -/
def SAT (w : List Bool) : Prop := ∃ a : List Bool, cnfSat (decodeCNF w) a

/-! ### The verifier's scan, and its correctness -/

/-- One left-to-right pass over the formula bits, mirroring the verifier machine exactly:
`bs` = assignment bits not yet used by the current clause, `as` = those used (reversed),
`fl` = current clause already satisfied. -/
def evalCNF : List Bool → List Bool → List Bool → Bool → Bool
  | false :: false :: r, bs, as, fl => fl && evalCNF r (as.reverse ++ bs) [] false
  | false :: true :: r, [], as, fl => evalCNF r [] as fl
  | false :: true :: r, x :: bs, as, fl => evalCNF r bs (x :: as) fl
  | true :: _ :: r, [], as, fl => evalCNF r [] as fl
  | true :: s :: r, x :: bs, as, fl => evalCNF r bs (x :: as) (fl || x == !s)
  | _, _, _, _ => true

/-- The same scan with an explicit position `j` in the current clause. -/
def evalIdx : List Bool → List Bool → ℕ → Bool → Bool
  | false :: false :: r, a, _, fl => fl && evalIdx r a 0 false
  | false :: true :: r, a, j, fl => evalIdx r a (j + 1) fl
  | true :: s :: r, a, j, fl => evalIdx r a (j + 1) (fl || a[j]? == some (!s))
  | _, _, _, _ => true

theorem evalCNF_eq_evalIdx (r a : List Bool) (j : ℕ) (fl : Bool) :
    evalCNF r (a.drop j) (a.take j).reverse fl = evalIdx r a j fl := by
  induction r, a, j, fl using evalIdx.induct with
  | case1 r a j fl ih =>
      simp [evalCNF, evalIdx, ← ih]
  | case2 r a j fl ih =>
      rw [evalIdx, ← ih]
      rcases h : a[j]? with _ | x
      · rw [List.getElem?_eq_none_iff] at h
        rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (by omega),
          List.take_of_length_le h, List.take_of_length_le (by omega), evalCNF]
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
        have ht : (a.take (j + 1)).reverse = a[j] :: (a.take j).reverse := by
          rw [List.take_add_one, h]; simp
        rw [List.drop_eq_getElem_cons hj, evalCNF, ht]
  | case3 s r a j fl ih =>
      rw [evalIdx, ← ih]
      rcases h : a[j]? with _ | x
      · rw [List.getElem?_eq_none_iff] at h
        rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (by omega),
          List.take_of_length_le h, List.take_of_length_le (by omega), evalCNF]
        simp
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
        have ht : (a.take (j + 1)).reverse = a[j] :: (a.take j).reverse := by
          rw [List.take_add_one, h]; simp
        rw [List.drop_eq_getElem_cons hj, evalCNF, ht]
        simp
  | case4 r a j fl h1 h2 h3 =>
      rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [evalCNF, evalIdx]

theorem clauseSat_nil (a : List Bool) : ¬ clauseSat [] a := by
  rintro ⟨j, b, h, -⟩; simp at h

theorem clauseSat_append_none (c : Clause) (a : List Bool) :
    clauseSat (c ++ [none]) a ↔ clauseSat c a := by
  constructor
  · rintro ⟨j, b, hj, ha⟩
    refine ⟨j, b, ?_, ha⟩
    rw [List.getElem?_append] at hj
    split_ifs at hj with h
    · exact hj
    · rcases hk : j - c.length with _ | k <;> simp [hk] at hj
  · rintro ⟨j, b, hj, ha⟩
    refine ⟨j, b, ?_, ha⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1, hj]

theorem clauseSat_append_some (c : Clause) (a : List Bool) (b : Bool) :
    clauseSat (c ++ [some b]) a ↔ clauseSat c a ∨ a[c.length]? = some b := by
  constructor
  · rintro ⟨j, b', hj, ha⟩
    rw [List.getElem?_append] at hj
    split_ifs at hj with h
    · exact Or.inl ⟨j, b', hj, ha⟩
    · rcases hk : j - c.length with _ | k
      · simp only [hk, List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        right
        rwa [show j = c.length by omega] at ha
      · simp [hk] at hj
  · rintro (⟨j, b', hj, ha⟩ | h)
    · refine ⟨j, b', ?_, ha⟩
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1, hj]
    · exact ⟨c.length, b, by simp, h⟩

theorem evalIdx_iff (r : List Bool) (cur : Clause) (a : List Bool) (fl : Bool)
    (hfl : fl = true ↔ clauseSat cur.reverse a) :
    evalIdx r a cur.length fl = true ↔ cnfSat (decodeAux r cur) a := by
  induction r, cur using decodeAux.induct generalizing fl with
  | case1 r cur ih =>
      have := ih false (by simp [clauseSat_nil])
      simp only [evalIdx, decodeAux, Bool.and_eq_true, cnfSat, List.mem_cons,
        forall_eq_or_imp] at this ⊢
      rw [List.length_nil] at this
      rw [this, hfl]
  | case2 r cur ih =>
      rw [evalIdx, decodeAux, ← ih fl (by rw [hfl, List.reverse_cons, clauseSat_append_none])]
      rfl
  | case3 s r cur ih =>
      rw [evalIdx, decodeAux]
      refine (Eq.to_iff rfl).trans (ih _ ?_)
      rw [List.reverse_cons, clauseSat_append_some, List.length_reverse, Bool.or_eq_true, hfl,
        beq_iff_eq]
  | case4 r cur h1 h2 h3 =>
      have hd : decodeAux r cur = [] := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [decodeAux]
      have he : evalIdx r a cur.length fl = true := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [evalIdx]
      simp [hd, he, cnfSat]

/-- The checking relation. -/
def check (w y : List Bool) : Bool := evalCNF w y [] false

theorem check_iff (w y : List Bool) : check w y = true ↔ cnfSat (decodeCNF w) y := by
  have h := evalCNF_eq_evalIdx w y 0 false
  simp only [List.drop_zero, List.take_zero, List.reverse_nil] at h
  rw [check, h]
  exact evalIdx_iff w [] y false (by simp [clauseSat_nil])

/-- Every decoded clause is no wider than the input. -/
theorem length_le_of_mem_decodeAux (r : List Bool) (cur : Clause) :
    ∀ c ∈ decodeAux r cur, c.length ≤ cur.length + r.length := by
  induction r, cur using decodeAux.induct with
  | case1 r cur ih =>
      intro c hc
      simp only [decodeAux, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · have := ih c hc; simp at this ⊢; omega
  | case2 r cur ih =>
      intro c hc; have := ih c hc; simp at this ⊢; omega
  | case3 s r cur ih =>
      intro c hc; have := ih c hc; simp at this ⊢; omega
  | case4 r cur h1 h2 h3 =>
      have hd : decodeAux r cur = [] := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [decodeAux]
      simp [hd]

/-- Truncating a satisfying assignment to the input length keeps it satisfying. -/
theorem cnfSat_take (w a : List Bool) (h : cnfSat (decodeCNF w) a) :
    cnfSat (decodeCNF w) (a.take w.length) := by
  intro c hc
  obtain ⟨j, b, hj, ha⟩ := h c hc
  have hlen := length_le_of_mem_decodeAux w [] c hc
  have hjc := (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨j, b, hj, ?_⟩
  rw [List.getElem?_take_of_lt (by simp at hlen; omega), ha]

/-- `SAT` is exactly "there is a short certificate accepted by `check`". -/
theorem sat_iff_check (w : List Bool) :
    SAT w ↔ ∃ y : List Bool, y.length ≤ w.length ^ 1 ∧ check w y = true := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.take w.length, by simp, (check_iff _ _).2 (cnfSat_take w a ha)⟩
  · rintro ⟨y, -, hy⟩
    exact ⟨y, (check_iff _ _).1 hy⟩

end Cslib.Complexity.DenseSAT
