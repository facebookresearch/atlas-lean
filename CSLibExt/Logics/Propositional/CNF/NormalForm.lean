/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equivalent conjunctive normal form by distribution
-/
module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics

/-!
# Equivalent conjunctive normal form by distribution

Every proposition is equivalent to a formula in conjunctive normal form.  This
file computes such a CNF, in the CSLibExt CNF representation, for upstream CSLib
propositions over any type of atoms named by `ι : Atom → ℕ`, and proves that it
has the same truth value as the proposition under every valuation.

The construction pushes Boolean complements to the atoms (as negative literals)
and distributes `∨` over `∧`. `cnfOf ι pos A` is a CNF of `A` (if `pos`) or of
its Boolean complement (true exactly when `A` is false), by recursion on the
polarity: `A ∨ B` becomes the clause-wise product of the CNFs of `A` and `B`,
and `A → B` the product of the complement's CNF of `A` with the CNF of `B`.
Each call builds only the polarity it needs, conjunction-like nodes thread an
accumulator (`cnfAcc`), and a chain of disjunction-like nodes is distributed one
disjunct at a time (`cnfOr`), so deep chains of either kind do not recopy their
partial results; no cost theorem is claimed. The complement is not upstream's
`¬A`, which is `A → ⊥` with `⊥` an atom; the two agree when `⊥` is false.

The output can be exponentially larger than the input, which is unavoidable for
an equivalent CNF (the parity function needs exponentially many clauses); the
Tseitin transformation (`CSLibExt/Algorithms/SAT/Tseitin`) is the linear-size,
equisatisfiable alternative.

## Main definitions

- `CNF.disj φ ψ` : the CNF of the disjunction of `φ` and `ψ`, one clause
  `C ++ D` for every pair of clauses.
- `Proposition.cnfAcc ι pos A acc`, `Proposition.cnfOr ι pos A S` : the builders
  (prepend to `acc`; disjoin with `S`).
- `Proposition.cnfOf ι pos A` : a CNF of `A` or of its Boolean complement, with
  the atom `a` as the variable `ι a`; `toCNF ι A` and `toNegCNF ι A` are its two
  polarities.

## Main results

- `Proposition.satisfies_cnfAcc_cnfOr` : the builders' semantics.
- `Proposition.satisfies_cnfOf` : `(cnfOf ι pos A).Satisfies σ ↔ A.evalBool (σ ∘ ι) = pos`
  for every assignment `σ`; `satisfies_toCNF_iff` and `satisfies_toNegCNF_iff`
  are its two polarities.
- `Proposition.cnfSat_toCNF_bot_iff` : for injective `ι`, `A.toCNF ι` with the
  unit clause `¬⊥` added is satisfiable iff `A` has a model with upstream's atom
  `⊥` false. (Without that clause the question is trivial: every proposition
  over atoms alone is true under the all-true valuation.)
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

namespace CNF

/-- The CNF of a disjunction: `(⋀ Cᵢ) ∨ (⋀ Dⱼ)` is `⋀ (Cᵢ ∨ Dⱼ)`. -/
def disj (φ ψ : CNF) : CNF := φ.flatMap fun C ↦ ψ.map fun D ↦ C ++ D

theorem satisfies_disj {σ : Nat → Bool} {φ ψ : CNF} :
    (disj φ ψ).Satisfies σ ↔ φ.Satisfies σ ∨ ψ.Satisfies σ := by
  simp only [disj, Satisfies, List.mem_flatMap, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    obtain ⟨⟨C, hC, hCs⟩, ⟨D, hD, hDs⟩⟩ := hneg
    obtain ⟨l, hl, hls⟩ := h _ C hC D hD rfl
    rcases List.mem_append.mp hl with hl | hl
    · exact hCs ⟨l, hl, hls⟩
    · exact hDs ⟨l, hl, hls⟩
  · rintro (h | h) _ C hC D _ rfl
    · obtain ⟨l, hl, hls⟩ := h C hC
      exact ⟨l, List.mem_append_left _ hl, hls⟩
    · obtain ⟨l, hl, hls⟩ := h D ‹_›
      exact ⟨l, List.mem_append_right _ hl, hls⟩

end CNF

variable {Atom : Type u}

namespace Proposition

mutual

/-- `cnfAcc ι pos A acc`: a CNF of `A` (if `pos`) or of its Boolean complement (if not),
prepended to `acc`, with atom `a` as variable `ι a`. Conjunction-like nodes thread the
accumulator; disjunction-like nodes go through `cnfOr`. -/
def cnfAcc (ι : Atom → ℕ) : Bool → Proposition Atom → CNF → CNF
  | pos, atom a, acc => [(ι a, pos)] :: acc
  | true, and A B, acc => cnfAcc ι true A (cnfAcc ι true B acc)
  | false, or A B, acc => cnfAcc ι false A (cnfAcc ι false B acc)
  | false, imp A B, acc => cnfAcc ι true A (cnfAcc ι false B acc)
  | true, or A B, acc => cnfOr ι true A (cnfAcc ι true B []) ++ acc
  | true, imp A B, acc => cnfOr ι false A (cnfAcc ι true B []) ++ acc
  | false, and A B, acc => cnfOr ι false A (cnfAcc ι false B []) ++ acc

/-- `cnfOr ι pos A S`: a CNF of `A` (or its complement) disjoined with the CNF `S`. A chain
of disjunction-like nodes is consumed from the left, so each step distributes one disjunct
over the CNF built so far, whatever the nesting. -/
def cnfOr (ι : Atom → ℕ) : Bool → Proposition Atom → CNF → CNF
  | true, or A B, S => cnfOr ι true A (cnfOr ι true B S)
  | true, imp A B, S => cnfOr ι false A (cnfOr ι true B S)
  | false, and A B, S => cnfOr ι false A (cnfOr ι false B S)
  | pos, atom a, S => CNF.disj [[(ι a, pos)]] S
  | true, and A B, S => CNF.disj (cnfAcc ι true A (cnfAcc ι true B [])) S
  | false, or A B, S => CNF.disj (cnfAcc ι false A (cnfAcc ι false B [])) S
  | false, imp A B, S => CNF.disj (cnfAcc ι true A (cnfAcc ι false B [])) S

end

/-- A CNF of `A` (if `pos`) or of its Boolean complement (if not), with atom `a` as variable
`ι a`. Each call builds only the polarity it is asked for: a CNF-shaped input gets a linear
`cnfOf ι true`, even though its complement is exponential. -/
def cnfOf (ι : Atom → ℕ) (pos : Bool) (A : Proposition Atom) : CNF := cnfAcc ι pos A []

/-- A CNF equivalent to `A`. -/
def toCNF (ι : Atom → ℕ) (A : Proposition Atom) : CNF := cnfOf ι true A

/-- A CNF of the Boolean complement of `A`: it holds exactly when `A` is false
(`satisfies_toNegCNF_iff`). This is not upstream's `¬A = A → ⊥`, which can be true when
`A` is, if the atom `⊥` is true. -/
def toNegCNF (ι : Atom → ℕ) (A : Proposition Atom) : CNF := cnfOf ι false A

theorem satisfies_cnfAcc_cnfOr (ι : Atom → ℕ) (A : Proposition Atom) (σ : Nat → Bool) :
    ∀ pos (acc S : CNF),
      ((cnfAcc ι pos A acc).Satisfies σ ↔ A.evalBool (σ ∘ ι) = pos ∧ acc.Satisfies σ) ∧
      ((cnfOr ι pos A S).Satisfies σ ↔ A.evalBool (σ ∘ ι) = pos ∨ S.Satisfies σ) := by
  induction A with
  | atom a =>
    intro pos acc S
    constructor
    · simp [cnfAcc]
    · simp only [cnfOr, CNF.satisfies_disj]
      simp
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    have hA1 : ∀ pos acc, (cnfAcc ι pos A acc).Satisfies σ ↔
        A.evalBool (σ ∘ ι) = pos ∧ acc.Satisfies σ := fun pos acc ↦ (ihA pos acc []).1
    have hA2 : ∀ pos S, (cnfOr ι pos A S).Satisfies σ ↔
        A.evalBool (σ ∘ ι) = pos ∨ S.Satisfies σ := fun pos S ↦ (ihA pos [] S).2
    have hB1 : ∀ pos acc, (cnfAcc ι pos B acc).Satisfies σ ↔
        B.evalBool (σ ∘ ι) = pos ∧ acc.Satisfies σ := fun pos acc ↦ (ihB pos acc []).1
    have hB2 : ∀ pos S, (cnfOr ι pos B S).Satisfies σ ↔
        B.evalBool (σ ∘ ι) = pos ∨ S.Satisfies σ := fun pos S ↦ (ihB pos [] S).2
    intro pos acc S
    cases pos <;> constructor <;>
    · simp only [cnfAcc, cnfOr, CNF.satisfies_append, CNF.satisfies_disj, hA1, hA2, hB1, hB2,
        evalBool, CNF.satisfies_nil]
      cases A.evalBool (σ ∘ ι) <;> cases B.evalBool (σ ∘ ι) <;> simp

theorem satisfies_cnfOf (ι : Atom → ℕ) (pos : Bool) (A : Proposition Atom) (σ : Nat → Bool) :
    (cnfOf ι pos A).Satisfies σ ↔ A.evalBool (σ ∘ ι) = pos := by
  rw [cnfOf, (satisfies_cnfAcc_cnfOr ι A σ pos [] []).1]
  simp

/-- **Equivalent CNF**: `A.toCNF ι` is satisfied by `σ` iff `A` is true under `σ ∘ ι`. -/
theorem satisfies_toCNF_iff (ι : Atom → ℕ) (A : Proposition Atom) (σ : Nat → Bool) :
    (A.toCNF ι).Satisfies σ ↔ A.evalBool (σ ∘ ι) = true :=
  satisfies_cnfOf ι true A σ

theorem satisfies_toNegCNF_iff (ι : Atom → ℕ) (A : Proposition Atom) (σ : Nat → Bool) :
    (A.toNegCNF ι).Satisfies σ ↔ A.evalBool (σ ∘ ι) = false :=
  satisfies_cnfOf ι false A σ

/-- With the atom `⊥` read as false: adding the unit clause `¬⊥` gives a CNF that is
satisfiable iff `A` has a model with `⊥` false. -/
theorem cnfSat_toCNF_bot_iff [Bot Atom] {ι : Atom → ℕ} (hι : Function.Injective ι)
    (A : Proposition Atom) :
    CNFSat ([(ι ⊥, false)] :: A.toCNF ι) ↔
      ∃ v : Atom → Bool, v ⊥ = false ∧ A.evalBool v = true := by
  rw [cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨σ, hσ⟩
    simp only [CNF.satisfies_cons, CNFClause.satisfies_def, List.mem_singleton,
      exists_eq_left] at hσ
    exact ⟨σ ∘ ι, hσ.1, (satisfies_toCNF_iff ι A σ).mp hσ.2⟩
  · rintro ⟨v, hv, hA⟩
    classical
    let σ : Nat → Bool := fun x ↦ if h : ∃ a, ι a = x then v h.choose else false
    have hcomp : σ ∘ ι = v := by
      funext a
      have h : ∃ a', ι a' = ι a := ⟨a, rfl⟩
      simp only [σ, Function.comp, h, dite_true]
      exact congrArg v (hι h.choose_spec)
    refine ⟨σ, ?_⟩
    simp only [CNF.satisfies_cons, CNFClause.satisfies_def, List.mem_singleton, exists_eq_left]
    refine ⟨?_, (satisfies_toCNF_iff ι A σ).mpr (hcomp ▸ hA)⟩
    have : σ (ι ⊥) = v ⊥ := congrFun hcomp ⊥
    rw [this, hv]

end Proposition

end Cslib.Logic.PL
