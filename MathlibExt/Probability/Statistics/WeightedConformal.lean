/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.WithBot
import Mathlib.Tactic.Linarith

/-!
# Weighted quantiles with an atom at infinity

Weighted conformal prediction (R. J. Tibshirani, R. F. Barber, E. J. Candès and A. Ramdas,
*Conformal prediction under covariate shift*, NeurIPS 2019, arXiv:1904.06019) replaces the
empirical quantile of the calibration scores by the level-`β` quantile of the discrete
distribution

`F = ∑ᵢ pᵢ δ_{vᵢ} + p_∞ δ_{+∞}`,

with nonnegative weights summing to `1`. Here the quantile of a distribution `F` on
`ℝ ∪ {+∞}` is `inf {t : F((-∞, t]) ≥ β}`. For `β ≤ 1` the atom at `+∞` matters only through the
total mass: the quantile is the least score `vⱼ` whose cumulative weight
`∑_{i : vᵢ ≤ vⱼ} pᵢ` reaches `β`, and `+∞` when no score does. `weightedQuantile` is defined that
way, and `coe_le_weightedQuantile_iff` gives the criterion used in coverage proofs: a real `x`
lies below the quantile iff the weight strictly below `x` is less than `β`.

## Main definitions

* `weightedQuantile β v p`: the level-`β` quantile of `∑ᵢ pᵢ δ_{vᵢ} + p_∞ δ_{+∞}`, in
  `WithTop ℝ`.

## Main results

* `coe_le_weightedQuantile_iff`: for `0 < β` and nonnegative weights,
  `x ≤ weightedQuantile β v p ↔ ∑_{i : vᵢ < x} pᵢ < β`.
* `weightedQuantile_eq_top_iff`: for `0 < β`, the quantile is `+∞` iff the total finite weight
  is below `β`.
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.Statistics.WeightedConformal

variable {ι : Type*} [Fintype ι]

/-- **Weighted quantile with an atom at `+∞`.** For a level `β`, scores `v : ι → ℝ` and weights
`p : ι → ℝ`, the least score `vⱼ` whose cumulative weight `∑_{i : vᵢ ≤ vⱼ} pᵢ` is at least `β`,
and `⊤` if there is none. When the `pᵢ` are nonnegative, the remaining mass `p_∞ = 1 - ∑ᵢ pᵢ`
is nonnegative and sits at `+∞`, and `0 < β ≤ 1`, this is the level-`β` quantile
`inf {t : F(t) ≥ β}` of `F = ∑ᵢ pᵢ δ_{vᵢ} + p_∞ δ_{+∞}`, the quantity
`Quantile(β; ∑ᵢ pᵢ δ_{vᵢ} + p_{n+1} δ_∞)` of Tibshirani, Barber, Candès and Ramdas (NeurIPS 2019,
arXiv:1904.06019, Corollary 1); the quantile theorems below assume `0 < β`. Outside that range it
is only the finite selection formula: for `β ≤ 0` with nonnegative weights every score qualifies
and the value is the least score, although every real threshold `t` has `F(t) ≥ β`. -/
noncomputable def weightedQuantile (β : ℝ) (v : ι → ℝ) (p : ι → ℝ) : WithTop ℝ :=
  (univ.filter fun j => β ≤ ∑ i ∈ univ.filter (fun i => v i ≤ v j), p i).inf
    fun j => ((v j : ℝ) : WithTop ℝ)

/-- **Criterion for lying below the weighted quantile.** For `0 < β` and nonnegative weights, a
real `x` is at most the weighted quantile iff the total weight of the scores strictly below `x`
is less than `β`. -/
theorem coe_le_weightedQuantile_iff {β : ℝ} (hβ : 0 < β) (v : ι → ℝ) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (x : ℝ) :
    (x : WithTop ℝ) ≤ weightedQuantile β v p ↔
      ∑ i ∈ univ.filter (fun i => v i < x), p i < β := by
  classical
  rw [weightedQuantile, Finset.le_inf_iff]
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have hne : (univ.filter fun i => v i < x).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.sum_empty] at hge
      exact absurd hge (not_le.2 hβ)
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image _ v hne
    have hjx : v j < x := (Finset.mem_filter.1 hj).2
    have hsets : (univ.filter fun i => v i ≤ v j) = univ.filter fun i => v i < x := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun hi => hi.trans_lt hjx
      · intro hi
        exact hjmax i (by simpa using hi)
    have := h j (by simpa [hsets] using hge)
    exact absurd (WithTop.coe_le_coe.1 this) (not_le.2 hjx)
  · intro hlt j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [WithTop.coe_le_coe]
    by_contra hjx
    push Not at hjx
    have hsub : (univ.filter fun i => v i ≤ v j) ⊆ univ.filter fun i => v i < x := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi.trans_lt hjx
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hp i
    linarith

/-- **The weighted quantile is infinite exactly when the finite weight is short.** For
`0 < β` and nonnegative weights, `weightedQuantile β v p = ⊤` iff `∑ᵢ pᵢ < β`, i.e. iff the
level `β` can only be reached with the atom at `+∞`. -/
theorem weightedQuantile_eq_top_iff {β : ℝ} (hβ : 0 < β) (v : ι → ℝ) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) :
    weightedQuantile β v p = ⊤ ↔ ∑ i, p i < β := by
  classical
  rw [weightedQuantile, Finset.inf_eq_top_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, WithTop.coe_ne_top, imp_false,
    not_le]
  constructor
  · intro h
    by_cases hemp : (univ : Finset ι).Nonempty
    · obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image univ v hemp
      have hall : (univ.filter fun i => v i ≤ v j) = univ := by
        ext i; simp [hjmax i (Finset.mem_univ i)]
      simpa [hall] using h j
    · rw [Finset.not_nonempty_iff_eq_empty] at hemp
      simpa [hemp] using hβ
  · intro h j
    exact lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ => hp i) h

end MathlibExt.Probability.Statistics.WeightedConformal
