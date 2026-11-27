/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.RobustStochasticApproximation

open MeasureTheory ProbabilityTheory Finset MathlibExt.Analysis.Convex.MirrorDescent

namespace MathlibExt.Analysis.Convex.RobustStochasticApproximation

/-- Constant random variables on the one-point probability space are independent. -/
theorem iIndepFun_unit {β : Type*} [MeasurableSpace β] (ξ : ℕ → Unit → β) :
    iIndepFun ξ (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, () ∈ ξ i ⁻¹' sets i
  · rw [Measure.dirac_apply_of_mem (Set.mem_iInter₂.mpr h), Finset.prod_eq_one]
    intro i hi
    exact Measure.dirac_apply_of_mem (h i hi)
  · push Not at h
    obtain ⟨i, hi, hni⟩ := h
    rw [Finset.prod_eq_zero hi (by simp [Measure.dirac_apply', hni])]
    simp only [Measure.dirac_apply', MeasurableSet.of_discrete, Set.indicator_apply_eq_zero]
    intro hmem
    exact absurd (Set.mem_iInter₂.mp hmem i hi) hni

/-- Projected (Euclidean mirror descent) steps on `[0, 1]`: `P x ξ = clamp (x - ξ 1)`. -/
noncomputable def projStep (x : ℝ) (ξ : ℝ →L[ℝ] ℝ) : ℝ := max 0 (min 1 (x - ξ 1))

-- Robust stochastic approximation for `f x = x` on `[0, 1]` with exact gradients `G = id`
-- (a degenerate noise on the one-point space), Euclidean setup, `γ = 1/2`, from `x₀ = 1`:
-- the expected error of the average is at most `(1 + ∑ γ² / 2) / ∑ γ` after `N ≥ 1` steps.
example (N : ℕ) (hN : 0 < N) :
    ∫ _s, ((∑ _t ∈ range N, (1 / 2 : ℝ))⁻¹ • ∑ t ∈ range N, (1 / 2 : ℝ) •
        (Nat.rec (1 : ℝ) (fun _ y => projStep y ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)) t :
          ℝ)) ∂(Measure.dirac (() : Unit)) - (0 : ℝ) ≤
      (1 ^ 2 + 1 ^ 2 * (∑ _t ∈ range N, (1 / 2 : ℝ) ^ 2) / (2 * 1)) /
        ∑ _t ∈ range N, (1 / 2 : ℝ) := by
  have hstep : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ ξ : ℝ →L[ℝ] ℝ, projStep x ξ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (ξ - x • ContinuousLinearMap.id ℝ ℝ +
        projStep x ξ • ContinuousLinearMap.id ℝ ℝ) (u - projStep x ξ) := by
    intro x _ ξ
    refine ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, fun u hu => ?_⟩
    simp only [projStep, add_apply, sub_apply,
      smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    have h1 : ξ (u - max 0 (min 1 (x - ξ 1))) = (u - max 0 (min 1 (x - ξ 1))) * ξ 1 := by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [h1]
    rcases hu with ⟨hu0, hu1⟩
    rcases le_total (x - ξ 1) 0 with h | h
    · rw [min_eq_right (h.trans zero_le_one), max_eq_left h]; nlinarith
    · rcases le_total (x - ξ 1) 1 with h' | h'
      · rw [min_eq_right h', max_eq_right h]; nlinarith
      · rw [min_eq_left h', max_eq_right zero_le_one]; nlinarith
  refine integral_robust_sa_average_sub_le (μ := Measure.dirac ()) (fun x : ℝ => x ^ 2 / 2)
    (fun x => x • ContinuousLinearMap.id ℝ ℝ) one_pos (X := Set.Icc 0 1) (Xo := Set.Icc 0 1)
    subset_rfl isCompact_Icc (fun x _ u _ => ?_) (P := projStep) ?_ hstep
    (f := fun x => x) (convexOn_id (convex_Icc 0 1)) continuousOn_id (ν := Measure.dirac ())
    (G := fun _ _ => ContinuousLinearMap.id ℝ ℝ) measurable_const (M := 1)
    (fun _ _ _ => ContinuousLinearMap.norm_id_le) (fun x _ y _ => ?_)
    (ξ := fun _ _ => ()) (fun _ => measurable_const) (iIndepFun_unit _)
    (fun _ => by simp) (x0 := 1) ⟨zero_le_one, le_rfl⟩ (γ := fun _ => 1 / 2) (fun _ => by norm_num)
    (x := fun t _ => Nat.rec (1 : ℝ)
      (fun _ y => projStep y ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)) t)
    (fun _ => rfl) (fun _ _ => rfl) (xstar := 0) ⟨le_rfl, zero_le_one⟩ (D := 1) ?_ hN
  · simp [bregman, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (u - x)]
  · refine Continuous.measurable ?_
    unfold projStep
    exact continuous_const.max (continuous_const.min (continuous_fst.sub
      (continuous_snd.clm_apply continuous_const)))
  · simp
  · simp [bregman]

end MathlibExt.Analysis.Convex.RobustStochasticApproximation
