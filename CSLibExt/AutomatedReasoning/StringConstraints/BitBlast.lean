/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.AutomatedReasoning.StringConstraints.WordEquations
public import CSLibExt.Algorithms.SAT.DPLL.Solver
import CSLibExt.Algorithms.SAT.DPLL.Correctness
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.List.Pi
public import Mathlib.Data.List.FinRange

/-!
# Bit-blasting word equations to the verified DPLL solver

At fixed variable lengths, each Boolean string variable becomes a vector of SAT
variables. Repeated occurrences share that vector. Constants use the reserved
SAT variable `0`, forced true; two implication clauses compare each pair of
corresponding bits. Unequal lengths produce an empty clause. A whole system
uses one shared SAT assignment, not independent satisfiability per equation.

This is a direct CNF encoding of the concatenation-only Boolean-alphabet
fragment. It is motivated by HAMPI's bounded reduction, not a formalization of
HAMPI's bit-vector or context-free-language encoding. No external SAT process
is invoked: the executable backend is CSLibExt's verified DPLL implementation.
`boundedWordSatB` enumerates the `(B + 1)^n` length profiles, including zero
lengths. `patternMatchB` derives a sufficient bound from the concrete target,
so callers need not supply a bound for that restricted unbounded problem.

The proofs include both translation directions, the embedding into the original
formula semantics, exact clause counts, and clause width at most two. These are
combinatorial output-size/search-space results, not `TimeM` or SAT-runtime bounds.
General word-equation decidability, a general computable solution-length bound,
Makanin's algorithm, PSPACE, and regex/CFG bit-blasting are not formalized.

## References

A. Kieżun, V. Ganesh, S. Artzi, P. J. Guo, P. Hooimeijer, M. D. Ernst,
*HAMPI: A Solver for Word Equations over Strings, Regular Expressions, and
Context-Free Grammars*, ACM TOSEM 21(4), 2012, Article 25. The direct CNF
construction here covers only the fixed-length Boolean-word-equation slice.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.AutomatedReasoning.StringConstraints

open Cslib.Logic.PL

variable {n : ℕ}

/-- **SAT variable index for a bit of a string variable.**
A positive SAT index for position `p` of variable `i`; `0` is reserved. -/
def bitVar (i p : ℕ) : ℕ := Nat.pair i p + 1

/-- **Bit-blasting a word into literals.**
Expand a word into literals at a fixed length for each string variable. -/
def blastWord (ℓ : Fin n → ℕ) (w : List (Bool ⊕ Fin n)) : List (ℕ × Bool) :=
  w.flatMap fun
    | .inl b => [(0, b)]
    | .inr i => List.ofFn (fun p : Fin (ℓ i) => (bitVar i.val p.val, true))

private def literalValue (v : ℕ → Bool) (l : ℕ × Bool) : Bool :=
  decide (v l.1 = l.2)

/-- **Clauses forcing two literals to be equal.**
Two implication clauses forcing equal truth values of two literals. -/
def iffClauses (a b : ℕ × Bool) : CNF :=
  [[(a.1, !a.2), b], [(b.1, !b.2), a]]

private theorem satisfies_iffClauses (v : ℕ → Bool) (a b : ℕ × Bool) :
    (iffClauses a b).Satisfies v ↔ literalValue v a = literalValue v b := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  simp only [iffClauses, CNF.satisfies_cons, CNF.satisfies_nil,
    CNFClause.satisfies_cons, CNFClause.satisfies_nil, CNFLiteral.satisfies_def,
    literalValue]
  cases hi : v i <;> cases hj : v j <;> cases a <;> cases b <;> simp

/-- **Position-wise equality clauses for literal vectors.**
Compare literal vectors position by position; a length mismatch emits an empty clause. -/
def equalWordClauses : List (ℕ × Bool) → List (ℕ × Bool) → CNF
  | [], [] => []
  | a :: as, b :: bs => iffClauses a b ++ equalWordClauses as bs
  | _, _ => [[]]

private theorem satisfies_equalWordClauses (v : ℕ → Bool)
    (as bs : List (ℕ × Bool)) :
    (equalWordClauses as bs).Satisfies v ↔
      as.map (literalValue v) = bs.map (literalValue v) := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [equalWordClauses]
  | cons a as ih =>
    cases bs with
    | nil => simp [equalWordClauses]
    | cons b bs =>
      rw [equalWordClauses, CNF.satisfies_append, satisfies_iffClauses, ih]
      simp only [List.map_cons, List.cons.injEq]

/-- **Clauses for a word equation with a length check.**
Short-circuit unequal lengths before emitting position-wise equality clauses. -/
def equationClauses (as bs : List (ℕ × Bool)) : CNF :=
  if as.length = bs.length then equalWordClauses as bs else [[]]

private theorem satisfies_equationClauses (v : ℕ → Bool)
    (as bs : List (ℕ × Bool)) :
    (equationClauses as bs).Satisfies v ↔
      as.map (literalValue v) = bs.map (literalValue v) := by
  by_cases h : as.length = bs.length
  · simp only [equationClauses, ite_eq_left h, satisfies_equalWordClauses]
  · have hmap : as.map (literalValue v) ≠ bs.map (literalValue v) := by
      intro heq
      exact h (by simpa using congrArg List.length heq)
    simp [equationClauses, h, hmap]

/-- **CNF encoding of a word-equation system at fixed lengths.**
CNF for a system at fixed lengths, with shared variables and one constant bit. -/
def blastSystem (ℓ : Fin n → ℕ) (eqs : List (WordEq Bool (Fin n))) : CNF :=
  [(0, true)] :: eqs.flatMap (fun e =>
    equationClauses (blastWord ℓ e.lhs) (blastWord ℓ e.rhs))

/-- **Decoding string values from a SAT assignment.**
Read each string variable's bits from a SAT assignment. -/
def decodeAssignment (ℓ : Fin n → ℕ) (v : ℕ → Bool) (i : Fin n) : List Bool :=
  List.ofFn (fun p : Fin (ℓ i) => v (bitVar i.val p.val))

/-- **Encoding a substitution as a SAT assignment.**
Encode a substitution as a total SAT assignment, using inverse pairing. -/
def encodeAssignment (σ : Fin n → List Bool) (x : ℕ) : Bool :=
  if x = 0 then true
  else if h : (Nat.unpair (x - 1)).1 < n then
    (σ ⟨(Nat.unpair (x - 1)).1, h⟩).getD (Nat.unpair (x - 1)).2 false
  else false

@[simp] private theorem encodeAssignment_zero (σ : Fin n → List Bool) :
    encodeAssignment σ 0 = true := rfl

@[simp] private theorem encodeAssignment_bitVar (σ : Fin n → List Bool)
    (i : Fin n) (p : ℕ) :
    encodeAssignment σ (bitVar i.val p) = (σ i).getD p false := by
  simp [encodeAssignment, bitVar, Nat.unpair_pair, i.isLt]

@[simp] private theorem decodeAssignment_length (ℓ : Fin n → ℕ)
    (v : ℕ → Bool) (i : Fin n) : (decodeAssignment ℓ v i).length = ℓ i := by
  simp [decodeAssignment]

private theorem decode_encode (ℓ : Fin n → ℕ) (σ : Fin n → List Bool)
    (hlen : ∀ i, (σ i).length = ℓ i) :
    decodeAssignment ℓ (encodeAssignment σ) = σ := by
  funext i
  apply List.ext_getElem
  · simp [hlen]
  · intro p hp hq
    simp only [decodeAssignment, List.getElem_ofFn, encodeAssignment_bitVar]
    exact List.getD_eq_getElem _ _ hq

private theorem map_blastWord (ℓ : Fin n → ℕ) (v : ℕ → Bool)
    (hv0 : v 0 = true) (w : List (Bool ⊕ Fin n)) :
    (blastWord ℓ w).map (literalValue v) = evalWord (decodeAssignment ℓ v) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | inl b =>
      cases b <;> simpa [blastWord, evalWord, literalValue, hv0] using ih
    | inr i =>
      simpa [blastWord, evalWord, List.map_ofFn, literalValue,
        decodeAssignment, Function.comp_def] using ih

private theorem satisfies_blastSystem (ℓ : Fin n → ℕ) (v : ℕ → Bool)
    (eqs : List (WordEq Bool (Fin n))) :
    (blastSystem ℓ eqs).Satisfies v ↔
      v 0 = true ∧ ∀ e ∈ eqs, e.Satisfies (decodeAssignment ℓ v) := by
  rw [blastSystem, CNF.satisfies_cons]
  simp only [CNFClause.satisfies_cons, CNFClause.satisfies_nil,
    CNFLiteral.satisfies_def, or_false]
  constructor
  · rintro ⟨hv0, hs⟩
    refine ⟨hv0, fun e he => ?_⟩
    have hc : (equationClauses (blastWord ℓ e.lhs) (blastWord ℓ e.rhs)).Satisfies v :=
      fun c hc => hs c (List.mem_flatMap.mpr ⟨e, he, hc⟩)
    have heq := (satisfies_equationClauses v _ _).mp hc
    simpa only [map_blastWord ℓ v hv0, WordEq.Satisfies] using heq
  · rintro ⟨hv0, hs⟩
    refine ⟨hv0, fun c hc => ?_⟩
    obtain ⟨e, he, hc⟩ := List.mem_flatMap.mp hc
    have hEq := hs e he
    have hcs : (equationClauses (blastWord ℓ e.lhs) (blastWord ℓ e.rhs)).Satisfies v :=
      (satisfies_equationClauses v _ _).mpr (by
        simpa only [map_blastWord ℓ v hv0, WordEq.Satisfies] using hEq)
    exact hcs c hc

/-- **Fixed-length bit-blasting is equisatisfiable.**
Fixed-length bit-blasting is satisfiability-preserving in both directions. -/
theorem cnfSat_blastSystem (ℓ : Fin n → ℕ) (eqs : List (WordEq Bool (Fin n))) :
    CNFSat (blastSystem ℓ eqs) ↔
      ∃ σ : Fin n → List Bool, (∀ i, (σ i).length = ℓ i) ∧
        ∀ e ∈ eqs, e.Satisfies σ := by
  rw [cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨_, hs⟩ := (satisfies_blastSystem ℓ v eqs).mp hv
    exact ⟨decodeAssignment ℓ v, decodeAssignment_length ℓ v, hs⟩
  · rintro ⟨σ, hlen, hs⟩
    refine ⟨encodeAssignment σ, (satisfies_blastSystem ℓ _ eqs).mpr ⟨rfl, ?_⟩⟩
    simpa only [decode_encode ℓ σ hlen] using hs

/-- **Fixed-length word-equation solver via DPLL.**
Solve the fixed-length system by bit-blasting and the verified DPLL solver. -/
def fixedLengthSatB (ℓ : Fin n → ℕ) (eqs : List (WordEq Bool (Fin n))) : Bool :=
  Cslib.Algorithms.SAT.DPLL.dpll (blastSystem ℓ eqs)

/-- **Correctness of the fixed-length SAT-backed solver.**
The executable SAT-backed procedure accepts exactly the fixed-length solutions. -/
theorem fixedLengthSatB_iff (ℓ : Fin n → ℕ) (eqs : List (WordEq Bool (Fin n))) :
    fixedLengthSatB ℓ eqs = true ↔
      ∃ σ : Fin n → List Bool, (∀ i, (σ i).length = ℓ i) ∧
        ∀ e ∈ eqs, e.Satisfies σ := by
  rw [fixedLengthSatB, Cslib.Algorithms.SAT.DPLL.dpll_eq_true_iff, cnfSat_blastSystem]

/-- **Enumeration of bounded length profiles.**
All bounded length profiles, using Mathlib's finite Cartesian-product enumeration. -/
def lengthProfiles (n B : ℕ) : List (Fin n → ℕ) :=
  ((List.finRange n).pi (fun _ => List.range (B + 1))).map
    (fun f i => f i (List.mem_finRange i))

/-- **Membership in the length-profile enumeration.**
The profile enumeration contains exactly the pointwise-bounded length assignments. -/
theorem mem_lengthProfiles (ℓ : Fin n → ℕ) (B : ℕ) :
    ℓ ∈ lengthProfiles n B ↔ ∀ i, ℓ i ≤ B := by
  rw [lengthProfiles, List.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩ i
    have hi := (List.mem_pi _ f).mp hf i (List.mem_finRange i)
    exact Nat.lt_succ_iff.mp (List.mem_range.mp hi)
  · intro h
    refine ⟨fun i _ => ℓ i, ?_, rfl⟩
    apply (List.mem_pi _ _).mpr
    intro i hi
    exact List.mem_range.mpr (Nat.lt_succ_iff.mpr (h i))

/-- **Bounded word-equation solver via DPLL.**
Solve bounded word equations by trying finite length profiles and calling DPLL. -/
def boundedWordSatB (B : ℕ) (eqs : List (WordEq Bool (Fin n))) : Bool :=
  (lengthProfiles n B).any (fun ℓ => fixedLengthSatB ℓ eqs)

/-- **Soundness and completeness of the bounded word-equation solver.**
The bounded SAT-backed solver is sound and complete, including empty strings. -/
theorem boundedWordSatB_iff (B : ℕ) (eqs : List (WordEq Bool (Fin n))) :
    boundedWordSatB B eqs = true ↔
      ∃ σ : Fin n → List Bool, (∀ i, (σ i).length ≤ B) ∧
        ∀ e ∈ eqs, e.Satisfies σ := by
  simp only [boundedWordSatB, List.any_eq_true, mem_lengthProfiles, fixedLengthSatB_iff]
  constructor
  · rintro ⟨ℓ, hℓ, σ, hlen, hs⟩
    exact ⟨σ, fun i => (hlen i).le.trans (hℓ i), hs⟩
  · rintro ⟨σ, hlen, hs⟩
    exact ⟨fun i => (σ i).length, hlen, σ, fun _ => rfl, hs⟩

/-- **Decision procedure for bounded Boolean word equations.**
An executable decision procedure for bounded Boolean-alphabet word equations. -/
def decidableBoundedWordEq (B : ℕ) (eqs : List (WordEq Bool (Fin n))) :
    Decidable (∃ σ : Fin n → List Bool, (∀ i, (σ i).length ≤ B) ∧
      ∀ e ∈ eqs, e.Satisfies σ) :=
  decidable_of_iff (boundedWordSatB B eqs = true) (boundedWordSatB_iff B eqs)

/-- **Size of the length-profile search.**
The complete length-profile search has `(B + 1)^n` entries. -/
theorem lengthProfiles_length (n B : ℕ) : (lengthProfiles n B).length = (B + 1) ^ n := by
  simpa [lengthProfiles, Multiset.pi_coe] using!
    (Multiset.card_pi (List.finRange n : Multiset (Fin n))
      (fun _ => (List.range (B + 1) : Multiset ℕ)))

private theorem equalWordClauses_length (as bs : List (ℕ × Bool))
    (h : as.length = bs.length) : (equalWordClauses as bs).length = 2 * as.length := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [equalWordClauses]
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have ht : as.length = bs.length := Nat.succ.inj h
      simp only [equalWordClauses, List.length_append, iffClauses,
        List.length_cons, List.length_nil, ih bs ht]
      omega

/-- **Clause count for one word equation.**
One empty clause for unequal lengths; otherwise two clauses per bit. -/
theorem equationClauses_length (as bs : List (ℕ × Bool)) :
    (equationClauses as bs).length =
      if as.length = bs.length then 2 * as.length else 1 := by
  by_cases h : as.length = bs.length
  · simp [equationClauses, h, equalWordClauses_length as bs h]
  · simp [equationClauses, h]

/-- **Exact clause count of the CNF encoding.**
Exact CNF size: one constant-bit clause plus the position clauses for every equation.
This is an output-size count, not a `TimeM` or DPLL runtime bound. -/
theorem blastSystem_length (ℓ : Fin n → ℕ) (eqs : List (WordEq Bool (Fin n))) :
    (blastSystem ℓ eqs).length = 1 + (eqs.map (fun e =>
      if (blastWord ℓ e.lhs).length = (blastWord ℓ e.rhs).length
      then 2 * (blastWord ℓ e.lhs).length else 1)).sum := by
  simp [blastSystem, List.length_flatMap, equationClauses_length, Nat.add_comm]

private theorem equalWordClauses_width (as bs : List (ℕ × Bool)) :
    ∀ c ∈ equalWordClauses as bs, c.length ≤ 2 := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [equalWordClauses]
  | cons a as ih =>
    cases bs with
    | nil => simp [equalWordClauses]
    | cons b bs =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · simp only [iffClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp
      · exact ih bs c hc

/-- **CNF encoding uses clauses of width at most two.**
Every emitted clause has at most two literals, including the constant unit clause. -/
theorem blastSystem_width (ℓ : Fin n → ℕ) (eqs : List (WordEq Bool (Fin n))) :
    ∀ c ∈ blastSystem ℓ eqs, c.length ≤ 2 := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · decide
  · obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
    unfold equationClauses at hc
    split at hc
    · exact equalWordClauses_width _ _ c hc
    · simp only [List.mem_singleton] at hc
      subst c
      decide

/-- **Satisfiability as acceptance by some bounded SAT search.**
A source system is satisfiable iff some bounded SAT search accepts.
This does not make failure at one bound a decision of general UNSAT. -/
theorem wordSystem_satisfiable_iff_exists_boundedSatB (eqs : List (WordEq Bool (Fin n))) :
    (∃ σ : Fin n → List Bool, ∀ e ∈ eqs, e.Satisfies σ) ↔
      ∃ B : ℕ, boundedWordSatB B eqs = true := by
  rw [wordSystem_satisfiable_iff_exists_bound]
  simp only [boundedWordSatB_iff]

/-- **Pattern-matching decision against a concrete target.**
Decide matching against a concrete target, with no bound supplied by the caller. -/
def patternMatchB (w : List (Bool ⊕ Fin n)) (target : List Bool) : Bool :=
  boundedWordSatB target.length [⟨w, target.map Sum.inl⟩]

/-- **Target length bounds the pattern-matching search.**
The target length is a sufficient search bound for unrestricted pattern matching. -/
theorem patternMatchB_iff (w : List (Bool ⊕ Fin n)) (target : List Bool) :
    patternMatchB w target = true ↔ ∃ σ : Fin n → List Bool, evalWord σ w = target := by
  simpa [patternMatchB, boundedWordSatB_iff, WordEq.Satisfies, evalWord,
    List.flatMap_map] using
    (patternMatch_iff_bounded w target).symm

/-- **Decidability of Boolean-word pattern matching.**
Executable decidability for unrestricted Boolean-word pattern matching. -/
def decidablePatternMatch (w : List (Bool ⊕ Fin n)) (target : List Bool) :
    Decidable (∃ σ : Fin n → List Bool, evalWord σ w = target) :=
  decidable_of_iff (patternMatchB w target = true) (patternMatchB_iff w target)

/-- **Linear size bound for bit-blasted words.**
Expanded words are at most linear in source-word length and the supplied bound.
Together with `blastSystem_length`, this bounds CNF output size, not solver time. -/
theorem blastWord_length_le (ℓ : Fin n → ℕ) (w : List (Bool ⊕ Fin n)) (B : ℕ)
    (h : ∀ i, ℓ i ≤ B) : (blastWord ℓ w).length ≤ max 1 B * w.length := by
  induction w with
  | nil => simp [blastWord]
  | cons a w ih =>
    cases a with
    | inl b =>
      simpa [blastWord, Nat.mul_add, Nat.add_comm] using
        Nat.add_le_add (le_max_left 1 B) ih
    | inr i =>
      simpa [blastWord, Nat.mul_add, Nat.add_comm] using
        Nat.add_le_add ((h i).trans (le_max_right 1 B)) ih

/-- **SAT backend agrees with the bounded formula semantics.**
The SAT backend decides the same bounded semantics as the existing formula language. -/
theorem boundedWordSatB_formula_iff (B : ℕ) (eqs : List (WordEq Bool (Fin n))) :
    boundedWordSatB B eqs = true ↔
      ∃ σ : Fin n → List Bool, (∀ i, (σ i).length ≤ B) ∧
        Sat σ (andChain (eqs.map WordEq.toFormula)) := by
  simp [boundedWordSatB_iff, sat_andChain]

end Cslib.AutomatedReasoning.StringConstraints
