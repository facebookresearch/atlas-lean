/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Horn satisfiability by least-model computation
-/
module

public import CSLibExt.Algorithms.SAT.DPLL.Solver
public import Mathlib.Data.Finset.Card

/-!
# Horn satisfiability by least-model computation

A *Horn clause* has at most one positive literal.  A satisfiable set of Horn
clauses has a least model: start with every variable false and repeatedly make
true the positive literal of each clause whose body (the variables of its
negative literals) is already true.  The formula is satisfiable iff this least
candidate satisfies it.

The development uses the CSLibExt CNF representation and the executable
satisfaction check `formulaSatisfied` of the DPLL solver.

## Main definitions

- `IsHorn φ` : every clause of `φ` has at most one positive literal.
- `derive φ T` : the variables of positive literals of clauses whose negative
  literals all have their variables in `T` (one forward-chaining step).
- `close φ T` : the least superset of `T` closed under `derive φ`, computed by
  iteration (well-founded on the number of variables of `φ` outside `T`).
- `leastModel φ` : the assignment that is true exactly on `close φ ∅`.
- `hornSat φ` : `formulaSatisfied (leastModel φ) φ`.

## Main results

- `leastModel_le` : for a Horn formula, `leastModel φ` is below every model.
- `satisfies_leastModel_iff` : a Horn formula is satisfiable iff `leastModel φ`
  satisfies it.
- `hornSat_eq_true_iff` : `hornSat` decides satisfiability of Horn formulas.

## References

- W. F. Dowling, J. H. Gallier, *Linear-time algorithms for testing the
  satisfiability of propositional Horn formulae*, J. Logic Programming 1(3),
  1984, 267-284.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.SAT.Horn

open Cslib.Logic.PL Cslib.Algorithms.SAT.DPLL

/-- A Horn formula: every clause has at most one positive literal. -/
def IsHorn (φ : CNF) : Prop :=
  ∀ C ∈ φ, ∀ l ∈ C, ∀ m ∈ C, l.2 = true → m.2 = true → l = m

instance (φ : CNF) : Decidable (IsHorn φ) := by
  unfold IsHorn
  infer_instance

/-- The negative literals of `C` all have their variables in `T`. -/
def bodyIn (T : Finset Nat) (C : CNFClause) : Bool :=
  C.all fun l ↦ l.2 || decide (l.1 ∈ T)

theorem bodyIn_eq_true_iff {T : Finset Nat} {C : CNFClause} :
    bodyIn T C = true ↔ ∀ l ∈ C, l.2 = false → l.1 ∈ T := by
  simp only [bodyIn, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine forall₂_congr fun l _ ↦ ?_
  cases l.2 <;> simp

/-- One forward-chaining step: the positive literals of the clauses whose bodies lie in
`T`. -/
def derive (φ : CNF) (T : Finset Nat) : Finset Nat :=
  ((φ.filter (bodyIn T)).flatMap fun C ↦ (C.filter (·.2)).map Prod.fst).toFinset

theorem mem_derive {φ : CNF} {T : Finset Nat} {x : Nat} :
    x ∈ derive φ T ↔ ∃ C ∈ φ, (∀ l ∈ C, l.2 = false → l.1 ∈ T) ∧ (x, true) ∈ C := by
  simp only [derive, List.mem_toFinset, List.mem_flatMap, List.mem_filter, List.mem_map,
    bodyIn_eq_true_iff]
  constructor
  · rintro ⟨C, ⟨hC, hbody⟩, ⟨y, b⟩, ⟨hl, hb⟩, rfl⟩
    simp only at hb
    subst hb
    exact ⟨C, hC, hbody, hl⟩
  · rintro ⟨C, hC, hbody, hx⟩
    exact ⟨C, ⟨hC, hbody⟩, (x, true), ⟨hx, rfl⟩, rfl⟩

theorem derive_mono {φ : CNF} {T S : Finset Nat} (h : T ⊆ S) : derive φ T ⊆ derive φ S := by
  intro x hx
  obtain ⟨C, hC, hbody, hxC⟩ := mem_derive.mp hx
  exact mem_derive.mpr ⟨C, hC, fun l hl hneg ↦ h (hbody l hl hneg), hxC⟩

theorem derive_subset_vars (φ : CNF) (T : Finset Nat) : derive φ T ⊆ φ.vars := by
  intro x hx
  obtain ⟨C, hC, -, hxC⟩ := mem_derive.mp hx
  exact CNF.mem_vars.mpr ⟨C, hC, true, hxC⟩

/-- The closure of `T` under forward chaining. -/
def close (φ : CNF) (T : Finset Nat) : Finset Nat :=
  if derive φ T ⊆ T then T else close φ (T ∪ derive φ T)
termination_by (φ.vars \ T).card
decreasing_by
  obtain ⟨x, hxD, hxT⟩ := Finset.not_subset.mp ‹¬derive φ T ⊆ T›
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun heq ↦ ?_⟩
  · exact Finset.sdiff_subset_sdiff le_rfl Finset.subset_union_left
  · have hx : x ∈ φ.vars \ T := Finset.mem_sdiff.mpr ⟨derive_subset_vars φ T hxD, hxT⟩
    rw [← heq, Finset.mem_sdiff] at hx
    exact hx.2 (Finset.mem_union_right _ hxD)

theorem subset_close (φ : CNF) (T : Finset Nat) : T ⊆ close φ T := by
  induction T using close.induct φ with
  | case1 T h => rw [close]; simp only [h, ↓reduceIte]; exact Finset.Subset.refl T
  | case2 T h ih =>
    rw [close]; simp only [h, ↓reduceIte]
    exact Finset.subset_union_left.trans ih

theorem derive_close_subset (φ : CNF) (T : Finset Nat) : derive φ (close φ T) ⊆ close φ T := by
  induction T using close.induct φ with
  | case1 T h => rw [close]; simp only [h, ↓reduceIte]
  | case2 T h ih => rw [close]; simp only [h, ↓reduceIte]; exact ih

theorem close_subset {φ : CNF} {T S : Finset Nat} (hT : T ⊆ S) (hS : derive φ S ⊆ S) :
    close φ T ⊆ S := by
  induction T using close.induct φ with
  | case1 T h => rw [close]; simp only [h, ↓reduceIte]; exact hT
  | case2 T h ih =>
    rw [close]; simp only [h, ↓reduceIte]
    exact ih (Finset.union_subset hT ((derive_mono hT).trans hS))

/-- The least model candidate: true exactly on the forward-chaining closure of `∅`. -/
def leastModel (φ : CNF) : Nat → Bool := fun x ↦ decide (x ∈ close φ ∅)

/-- **Least model**: on a Horn formula, `leastModel φ` makes true only variables that every
model makes true. -/
theorem leastModel_le {φ : CNF} (hφ : IsHorn φ) {σ : Nat → Bool} (hσ : φ.Satisfies σ)
    {x : Nat} (hx : leastModel φ x = true) : σ x = true := by
  let S := φ.vars.filter fun y ↦ σ y = true
  have hS : derive φ S ⊆ S := by
    intro y hy
    obtain ⟨C, hC, hbody, hyC⟩ := mem_derive.mp hy
    obtain ⟨l, hl, hlsat⟩ := hσ C hC
    have hpos : l.2 = true := by
      by_contra hneg
      have hl1 := (Finset.mem_filter.mp (hbody l hl (by simpa using hneg))).2
      simp only [CNFLiteral.Satisfies] at hlsat
      rw [hl1] at hlsat
      exact hneg hlsat.symm
    have hly : l = (y, true) := hφ C hC l hl _ hyC hpos rfl
    subst hly
    exact Finset.mem_filter.mpr ⟨derive_subset_vars φ S hy, hlsat⟩
  have hsub := close_subset (Finset.empty_subset S) hS
  exact (Finset.mem_filter.mp (hsub (of_decide_eq_true hx))).2

/-- A Horn formula is satisfiable iff its least model candidate satisfies it. -/
theorem satisfies_leastModel_iff {φ : CNF} (hφ : IsHorn φ) :
    φ.Satisfies (leastModel φ) ↔ CNFSat φ := by
  refine ⟨fun h ↦ cnfSat_iff_exists_satisfies.mpr ⟨_, h⟩, fun hsat ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := cnfSat_iff_exists_satisfies.mp hsat
  intro C hC
  by_cases hbody : ∀ l ∈ C, l.2 = false → l.1 ∈ close φ ∅
  · by_cases hhead : ∃ l ∈ C, l.2 = true
    · obtain ⟨⟨x, b⟩, hl, hb⟩ := hhead
      simp only at hb
      subst hb
      have hx : x ∈ close φ ∅ := derive_close_subset φ ∅ (mem_derive.mpr ⟨C, hC, hbody, hl⟩)
      exact ⟨(x, true), hl, by simp [CNFLiteral.Satisfies, leastModel, hx]⟩
    · -- a goal clause whose body is in the least model is false in every model
      exfalso
      simp only [not_exists, not_and, Bool.not_eq_true] at hhead
      obtain ⟨l, hl, hlsat⟩ := hσ C hC
      have hneg := hhead l hl
      have htrue := leastModel_le hφ hσ (x := l.1) (by simp [leastModel, hbody l hl hneg])
      simp only [CNFLiteral.Satisfies] at hlsat
      rw [htrue, hneg] at hlsat
      exact absurd hlsat (by decide)
  · simp only [not_forall] at hbody
    obtain ⟨l, hl, hneg, hnot⟩ := hbody
    exact ⟨l, hl, by simp [CNFLiteral.Satisfies, leastModel, hnot, hneg]⟩

/-- Horn satisfiability: evaluate the formula at its least model candidate. -/
def hornSat (φ : CNF) : Bool := formulaSatisfied (leastModel φ) φ

/-- **Correctness**: `hornSat` decides satisfiability of Horn formulas. -/
theorem hornSat_eq_true_iff {φ : CNF} (hφ : IsHorn φ) : hornSat φ = true ↔ CNFSat φ := by
  rw [hornSat, formulaSatisfied_eq_true_iff, satisfies_leastModel_iff hφ]

end Cslib.Algorithms.SAT.Horn
