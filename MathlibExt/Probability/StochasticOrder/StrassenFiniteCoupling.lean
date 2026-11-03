/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.StrassenCoupling

/-!
# Strassen's theorem on a finite poset, with `ℝ≥0`-valued couplings

For a finite poset `P` and `μ ν : P → ℝ≥0` of equal total mass, `μ` is stochastically dominated by
`ν` (`μ(U) ≤ ν(U)` for every up-set `U`) iff there is a monotone coupling: `π : P × P → ℝ≥0` with
marginals `μ` and `ν`, supported on pairs `x ≤ y`.

The hard direction is a thin adapter to
`MathlibExt.Probability.StrassenCouplingWanted.forall_isUpperSet_sum_le_iff_exists_coupling`
(the same statement for real-valued nonnegative weights, proved by a combinatorial
induction): coerce the `ℝ≥0` weights to `ℝ`, apply that theorem, and convert the resulting
nonnegative coupling back with `Real.toNNReal`.
`StatMech.Probability.stochasticDom_iff_forall_isUpperSet` relates the two hypothesis forms.

## Main definitions

* `StatMech.Probability.IsCoupling`, `StatMech.Probability.IsMonotoneCoupling`: couplings and
  couplings supported on `x ≤ y`.
* `StatMech.Probability.StochasticDom`: domination on up-sets.

## Main results

* `StatMech.Probability.StochasticDom.of_isMonotoneCoupling`: the easy direction.
* `StatMech.Probability.exists_isMonotoneCoupling_of_stochasticDom`: the hard direction.
* `StatMech.Probability.strassen_finite`: **Strassen's theorem** for finite posets.

## References

* V. Strassen, *The existence of probability measures with given marginals*, Ann. Math.
  Statist. 36 (1965), 423–439.
-/

@[expose] public section

open Finset
open scoped NNReal

namespace StatMech
namespace Probability

variable {P : Type*}

section Defs

variable [Fintype P]

/-- A coupling of `μ` and `ν`: a weight on `P × P` with first marginal `μ` and second
marginal `ν`. -/
structure IsCoupling [PartialOrder P] (μ ν : P → ℝ≥0) (π : P × P → ℝ≥0) : Prop where
  fst_marginal : ∀ x, ∑ y, π (x, y) = μ x
  snd_marginal : ∀ y, ∑ x, π (x, y) = ν y

/-- A monotone coupling of `μ` and `ν`: a coupling supported on the pairs `x ≤ y`. -/
structure IsMonotoneCoupling [PartialOrder P] (μ ν : P → ℝ≥0) (π : P × P → ℝ≥0) : Prop
    extends IsCoupling μ ν π where
  supported : ∀ x y, ¬ x ≤ y → π (x, y) = 0

/-- `μ` is stochastically dominated by `ν`: `μ(U) ≤ ν(U)` for every up-set `U`. -/
def StochasticDom [Preorder P] (μ ν : P → ℝ≥0) : Prop :=
  ∀ U : Finset P, (∀ ⦃a b⦄, a ≤ b → a ∈ U → b ∈ U) → ∑ x ∈ U, μ x ≤ ∑ x ∈ U, ν x

omit [Fintype P] in
/-- `StochasticDom` is domination on the finsets that are upper sets in the sense of `IsUpperSet`;
this is the hypothesis form of
`MathlibExt.Probability.StrassenCouplingWanted.forall_isUpperSet_sum_le_iff_exists_coupling`. -/
theorem stochasticDom_iff_forall_isUpperSet [Preorder P] {μ ν : P → ℝ≥0} :
    StochasticDom μ ν ↔ ∀ U : Finset P, IsUpperSet (U : Set P) → ∑ x ∈ U, μ x ≤ ∑ x ∈ U, ν x :=
  Iff.rfl

end Defs

section Easy

variable [Fintype P] [PartialOrder P] [DecidableEq P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]

omit [DecidableEq P] [DecidableRel ((· ≤ ·) : P → P → Prop)] in
/-- A monotone coupling witnesses stochastic domination (the easy half of Strassen's theorem). -/
theorem StochasticDom.of_isMonotoneCoupling {μ ν : P → ℝ≥0} {π : P × P → ℝ≥0}
    (h : IsMonotoneCoupling μ ν π) : StochasticDom μ ν := by
  classical
  intro U hU
  have hμU : ∑ x ∈ U, μ x = ∑ p ∈ U ×ˢ (univ : Finset P), π p := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl (fun x _ => (h.fst_marginal x).symm)
  have hνU : ∑ y ∈ U, ν y = ∑ p ∈ (univ : Finset P) ×ˢ U, π p := by
    rw [Finset.sum_product, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => (h.snd_marginal y).symm)
  rw [hμU, hνU]
  have hLHS : ∑ p ∈ U ×ˢ (univ : Finset P), π p
      = ∑ p ∈ (U ×ˢ (univ : Finset P)).filter (fun p => p.1 ≤ p.2), π p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p.1 ≤ p.2
    · rw [ite_eq_left hp]
    · rw [ite_eq_right hp]; exact h.supported p.1 p.2 hp
  rw [hLHS]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hU hp.2 hp.1
  · intro p _ _; exact zero_le

end Easy

section Hard

variable [Fintype P] [DecidableEq P] [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]

/-- Stochastic domination with equal total mass yields a monotone coupling (the hard half of
Strassen's theorem), as a thin adapter to
`MathlibExt.Probability.StrassenCouplingWanted.forall_isUpperSet_sum_le_iff_exists_coupling`. -/
theorem exists_isMonotoneCoupling_of_stochasticDom {μ ν : P → ℝ≥0}
    (hTOT : ∑ x, μ x = ∑ x, ν x) (hSD : StochasticDom μ ν) :
    ∃ π : P × P → ℝ≥0, IsMonotoneCoupling μ ν π := by
  classical
  rcases isEmpty_or_nonempty P with hP | hP
  · refine ⟨fun _ => 0, ⟨⟨fun x => (IsEmpty.false x).elim, fun y => (IsEmpty.false y).elim⟩,
      fun x => (IsEmpty.false x).elim⟩⟩
  · have hsum : ∑ x, (μ x : ℝ) = ∑ x, (ν x : ℝ) := by exact_mod_cast hTOT
    have hUpper : ∀ U : Finset P, IsUpperSet (U : Set P) →
        ∑ x ∈ U, (μ x : ℝ) ≤ ∑ x ∈ U, (ν x : ℝ) := by
      intro U hU
      have h := (stochasticDom_iff_forall_isUpperSet (μ := μ) (ν := ν)).mp hSD U hU
      exact_mod_cast h
    obtain ⟨π, hpos, hrow, hcol, hsupp⟩ :=
      (MathlibExt.Probability.StrassenCouplingWanted.forall_isUpperSet_sum_le_iff_exists_coupling
        (fun x => (μ x : ℝ)) (fun x => (ν x : ℝ))
        (fun x => (μ x).coe_nonneg) (fun x => (ν x).coe_nonneg) hsum).mp hUpper
    refine ⟨fun p => (π p.1 p.2).toNNReal, ⟨⟨fun x => ?_, fun y => ?_⟩, fun x y h => ?_⟩⟩
    · have hcoe : ((∑ y, (π x y).toNNReal : ℝ≥0) : ℝ) = (μ x : ℝ) := by
        push_cast
        rw [Finset.sum_congr rfl (fun y _ => Real.coe_toNNReal _ (hpos x y)), hrow x]
      exact_mod_cast hcoe
    · have hcoe : ((∑ x, (π x y).toNNReal : ℝ≥0) : ℝ) = (ν y : ℝ) := by
        push_cast
        rw [Finset.sum_congr rfl (fun x _ => Real.coe_toNNReal _ (hpos x y)), hcol y]
      exact_mod_cast hcoe
    · rw [hsupp x y h, Real.toNNReal_zero]

end Hard

section Iff

variable [Fintype P] [PartialOrder P]

/-- **Strassen's theorem** on a finite poset: for `μ ν : P → ℝ≥0` of equal total mass, `μ` is
stochastically dominated by `ν` iff a monotone coupling exists. See also
`MathlibExt.Probability.StrassenCouplingWanted.forall_isUpperSet_sum_le_iff_exists_coupling`
(same statement, real-valued weights). V. Strassen, *The existence of probability measures with
given marginals*, 1965. -/
theorem strassen_finite {μ ν : P → ℝ≥0} (hTOT : ∑ x, μ x = ∑ x, ν x) :
    StochasticDom μ ν ↔ ∃ π : P × P → ℝ≥0, IsMonotoneCoupling μ ν π := by
  constructor
  · intro hSD; exact exists_isMonotoneCoupling_of_stochasticDom hTOT hSD
  · rintro ⟨π, hπ⟩; exact StochasticDom.of_isMonotoneCoupling hπ

end Iff

end Probability
end StatMech
