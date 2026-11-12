/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern
public import MathlibExt.Probability.StrassenCoupling

import Mathlib.Tactic

@[expose] public section

/-!
# First-order stochastic dominance and expected utility

Lotteries are points of `Convexity.StdSimplex ℝ α` over a finite linearly ordered prize set `α`,
with `expectedUtility` from `MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern`. The
lottery `q` first-order dominates `p` when its CDF lies weakly below that of `p` at every threshold.
In a linear order this is the upper-set dominance of the finite Strassen theorem
(`MathlibExt.Probability.StrassenCoupling`), which yields a monotone coupling; summing
`u y - u x ≥ 0` over the coupling shows that dominance raises expected utility for every increasing
utility. This is the economic (CDF) dominance of monetary lotteries, not the configuration-space
order `StatMech.StochasticallyDominated`.

## Main results

* `FirstOrderDominates.sum_le_of_isUpperSet`: CDF dominance implies upper-set dominance.
* `expectedUtility_le_of_monotoneCoupling`: a monotone coupling transfers expected utility.
* `expectedUtility_le_of_firstOrderDominates_of_strassen`: the composition, given Strassen.
* `expectedUtility_le_of_firstOrderDominates`: the result, citing
  `forall_isUpperSet_sum_le_iff_exists_coupling`.

## References

* J. Hadar and W. R. Russell, "Rules for ordering uncertain prospects", American Economic Review
  59 (1969), 25--34.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), Section 6.D (first-order stochastic dominance).
-/

namespace MathlibExt.Economics.Risk

open Convexity MathlibExt.Economics.ExpectedUtility MathlibExt.Probability.StrassenCouplingWanted

/-- First-order stochastic dominance of lotteries on a finite linearly ordered set of prizes:
`q` dominates `p` when, at every threshold `t`, `q` puts at most as much probability as `p` on
prizes `≤ t` (the CDF of `q` lies weakly below the CDF of `p`). -/
def FirstOrderDominates {α : Type*} [Fintype α] [LinearOrder α] (q p : StdSimplex ℝ α) : Prop :=
  ∀ t : α, ∑ x ∈ Finset.univ.filter (· ≤ t), q.weights x ≤
    ∑ x ∈ Finset.univ.filter (· ≤ t), p.weights x

/-- First-order dominance in CDF form gives the upper-set dominance of Strassen's theorem:
`q` puts at least as much probability as `p` on every upward-closed set of prizes. -/
theorem FirstOrderDominates.sum_le_of_isUpperSet {α : Type*} [Fintype α] [LinearOrder α]
    {q p : StdSimplex ℝ α} (h : FirstOrderDominates q p) (U : Finset α) (hU : IsUpperSet U) :
    ∑ x ∈ U, p.weights x ≤ ∑ x ∈ U, q.weights x := by
  classical
  by_cases hUempty : U = ∅
  · subst hUempty
    simp
  by_cases hUuniv : U = Finset.univ
  · subst hUuniv
    rw [p.total_of_fintype, q.total_of_fintype]
  · have hVne : (Finset.univ \ U).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hcon
      apply hUuniv
      have hsub : Finset.univ ⊆ U := Finset.sdiff_eq_empty_iff_subset.mp hcon
      exact le_antisymm (Finset.subset_univ U) hsub
    set t : α := (Finset.univ \ U).max' hVne with htdef
    have htU : t ∉ U := (Finset.mem_sdiff.mp (Finset.max'_mem _ hVne)).2
    have hVU : Finset.univ \ U = Finset.univ.filter (· ≤ t) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · intro hx
        have hxmem : x ∈ Finset.univ \ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
        exact Finset.le_max' _ x hxmem
      · intro hle hxU
        exact htU (hU hxU hle)
    have hV : ∑ x ∈ Finset.univ \ U, q.weights x ≤ ∑ x ∈ Finset.univ \ U, p.weights x := by
      rw [hVU]
      exact h t
    have htot : ∀ w : StdSimplex ℝ α,
        ∑ x ∈ U, w.weights x = 1 - ∑ x ∈ Finset.univ \ U, w.weights x := by
      intro w
      have h2 := Finset.sum_sdiff (Finset.subset_univ U) (f := w.weights)
      rw [w.total_of_fintype] at h2
      linarith
    rw [htot p, htot q]
    linarith

/-- A monotone coupling transfers expected utility: if `π ≥ 0` has marginals `p` and `q` and
is supported on pairs `x ≤ y`, then `E_p[u] ≤ E_q[u]` for every monotone `u`. -/
theorem expectedUtility_le_of_monotoneCoupling {α : Type*} [Fintype α] [LinearOrder α]
    {p q : StdSimplex ℝ α} {u : α → ℝ} (hu : Monotone u) (π : α → α → ℝ)
    (hπ : ∀ x y, 0 ≤ π x y) (hrow : ∀ x, ∑ y, π x y = p.weights x)
    (hcol : ∀ y, ∑ x, π x y = q.weights y) (hsupp : ∀ x y, ¬ x ≤ y → π x y = 0) :
    expectedUtility u p ≤ expectedUtility u q := by
  classical
  change ∑ x, p.weights x * u x ≤ ∑ x, q.weights x * u x
  calc ∑ x, p.weights x * u x
      = ∑ x, ∑ y, π x y * u x := by
        apply Finset.sum_congr rfl; intro x _
        rw [← hrow x, Finset.sum_mul]
    _ ≤ ∑ x, ∑ y, π x y * u y := by
        apply Finset.sum_le_sum; intro x _
        apply Finset.sum_le_sum; intro y _
        by_cases hxy : x ≤ y
        · exact mul_le_mul_of_nonneg_left (hu hxy) (hπ x y)
        · rw [hsupp x y hxy, zero_mul, zero_mul]
    _ = ∑ y, q.weights y * u y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro y _
        rw [← hcol y, Finset.sum_mul]

/-- **First-order stochastic dominance raises expected utility**, for every increasing utility,
given the finite Strassen coupling theorem `hS` (the forward direction of Atlas
`forall_isUpperSet_sum_le_iff_exists_coupling`, discharged in Atlas by citing it). -/
theorem expectedUtility_le_of_firstOrderDominates_of_strassen {α : Type*} [Fintype α]
    [LinearOrder α]
    (hS : ∀ p q : α → ℝ, (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) → ∑ x, p x = ∑ x, q x →
      (∀ U : Finset α, IsUpperSet U → ∑ x ∈ U, p x ≤ ∑ x ∈ U, q x) →
      ∃ π : α → α → ℝ, (∀ x y, 0 ≤ π x y) ∧ (∀ x, ∑ y, π x y = p x) ∧
        (∀ y, ∑ x, π x y = q y) ∧ (∀ x y, ¬ x ≤ y → π x y = 0))
    {q p : StdSimplex ℝ α} (h : FirstOrderDominates q p) {u : α → ℝ} (hu : Monotone u) :
    expectedUtility u p ≤ expectedUtility u q := by
  classical
  obtain ⟨π, hπ, hrow, hcol, hsupp⟩ := hS (fun x => p.weights x) (fun x => q.weights x)
    (fun x => Finsupp.le_def.mp p.nonneg x)
    (fun x => Finsupp.le_def.mp q.nonneg x)
    (by show ∑ x, p.weights x = ∑ x, q.weights x
        rw [p.total_of_fintype, q.total_of_fintype])
    (fun U hU => FirstOrderDominates.sum_le_of_isUpperSet h U hU)
  exact expectedUtility_le_of_monotoneCoupling hu π hπ hrow hcol hsupp

/-- **First-order stochastic dominance raises expected utility.** If `q` first-order dominates
`p` on a finite linearly ordered prize set, then `E_p[u] ≤ E_q[u]` for every increasing utility
`u`; the coupling comes from the finite Strassen theorem
`forall_isUpperSet_sum_le_iff_exists_coupling`. -/
theorem expectedUtility_le_of_firstOrderDominates {α : Type*} [Fintype α] [LinearOrder α]
    {q p : StdSimplex ℝ α} (h : FirstOrderDominates q p) {u : α → ℝ} (hu : Monotone u) :
    expectedUtility u p ≤ expectedUtility u q :=
  expectedUtility_le_of_firstOrderDominates_of_strassen
    (fun p q hp hq hsum => (forall_isUpperSet_sum_le_iff_exists_coupling p q hp hq hsum).mp) h hu

end MathlibExt.Economics.Risk
