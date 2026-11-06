/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Hölder boundary values from a gradient bound

If `F : ℂ → ℂ` is continuous on the closed unit disc, real-differentiable on the open disc, and
`‖fderiv ℝ F z‖ ≤ C (1 - ‖z‖)^(α - 1)` there for some `0 < α ≤ 1`, then its boundary values
`t ↦ F (circleMap 0 1 t)` are `α`-Hölder (`Complex.holderWith_circleMap_of_norm_fderiv_le`).

For `|t₁ - t₂| < 1` the proof compares `F` on the unit circle with `F` on the circle of radius
`1 - |t₁ - t₂|`: each radial segment costs `(C / α) |t₁ - t₂|^α`, and the arc between the two
inner points costs `C |t₁ - t₂|^α`, by the mean value inequality
(`Convex.norm_image_sub_le_of_norm_fderiv_le`). For `|t₁ - t₂| ≥ 1` both boundary values are
compared with `F 0`.

Code-derived port of `HolderBoundary.holder_boundary_of_gradient_bound` and its helpers from
`v1/Atlas/FourierAnalysis/code/BrownianMotion.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 2955–3232 (Lemma 5 of Chapter 1, Brownian
Motion). The public statement inlines the archived `SatisfiesGradientBound` predicate and states
the conclusion as Mathlib's `HolderWith`; the archived explicit bound
`‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤ C' |t₁ - t₂|^α` is the private
`holder_boundary_of_gradient_bound`. The archived formalization and its original
license/provenance remain in `v1/` (the original license text is `v1/LICENSE`). This records
equivalence to the archived Lean statement, not verification against the printed textbook.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Complex

/-- The interior gradient bound `‖F′(z)‖ ≤ C (1 - ‖z‖)^(α - 1)` on the open unit disc. -/
def SatisfiesGradientBound (F : ℂ → ℂ) (C : ℝ) (α : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 → ‖fderiv ℝ F z‖ ≤ C * (1 - ‖z‖) ^ (-1 + α)

theorem arc_segment_bound
    (F : ℂ → ℂ) (C₀ : ℝ) (α : ℝ) (ρ : ℝ) (t₁ t₂ : ℝ)
    (hC₀ : 0 ≤ C₀) (_hα_pos : 0 < α) (hα_le : α ≤ 1)
    (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ 1)
    (hdiff : DifferentiableOn ℝ F (Metric.ball 0 1))
    (hgrad : SatisfiesGradientBound F C₀ α)
    (ht : |t₁ - t₂| ≤ ρ) :
    ‖F (circleMap 0 (1 - ρ) t₁) - F (circleMap 0 (1 - ρ) t₂)‖ ≤ C₀ * ρ ^ α := by
  have h1mρ_nn : (0 : ℝ) ≤ 1 - ρ := by linarith
  have hcb_sub_b : Metric.closedBall (0 : ℂ) (1 - ρ) ⊆ Metric.ball 0 1 := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hdiffAt : ∀ z ∈ Metric.closedBall (0 : ℂ) (1 - ρ), DifferentiableAt ℝ F z := by
    intro z hz
    exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (hcb_sub_b hz))
  have hgrad_bound : ∀ z ∈ Metric.closedBall (0 : ℂ) (1 - ρ),
      ‖fderiv ℝ F z‖ ≤ C₀ * ρ ^ (-1 + α) := by
    intro z hz
    have hz_in_ball : ‖z‖ < 1 := by
      have := hcb_sub_b hz; simp only [Metric.mem_ball, dist_zero_right] at this; exact this
    have hz_norm_le : ‖z‖ ≤ 1 - ρ := by
      simp only [Metric.mem_closedBall, dist_zero_right] at hz; exact hz
    calc ‖fderiv ℝ F z‖
        ≤ C₀ * (1 - ‖z‖) ^ (-1 + α) := hgrad z hz_in_ball
      _ ≤ C₀ * ρ ^ (-1 + α) := by
          apply mul_le_mul_of_nonneg_left _ hC₀
          exact Real.rpow_le_rpow_of_nonpos hρ_pos (by linarith) (by linarith)
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    hdiffAt hgrad_bound (convex_closedBall 0 (1 - ρ))
    (circleMap_mem_closedBall 0 h1mρ_nn t₂)
    (circleMap_mem_closedBall 0 h1mρ_nn t₁)
  have hlip_bound : ‖circleMap 0 (1 - ρ) t₁ - circleMap 0 (1 - ρ) t₂‖ ≤ ρ := by
    have hlip := (lipschitzWith_circleMap 0 (1 - ρ)).dist_le_mul t₁ t₂
    rw [Complex.dist_eq, Real.dist_eq] at hlip
    calc ‖circleMap 0 (1 - ρ) t₁ - circleMap 0 (1 - ρ) t₂‖
        ≤ ↑(Real.nnabs (1 - ρ)) * |t₁ - t₂| := hlip
      _ = |1 - ρ| * |t₁ - t₂| := by simp [Real.coe_nnabs]
      _ = (1 - ρ) * |t₁ - t₂| := by rw [abs_of_nonneg h1mρ_nn]
      _ ≤ 1 * ρ := mul_le_mul (by linarith) ht (abs_nonneg _) (by linarith)
      _ = ρ := one_mul ρ
  calc ‖F (circleMap 0 (1 - ρ) t₁) - F (circleMap 0 (1 - ρ) t₂)‖
      ≤ C₀ * ρ ^ (-1 + α) * ‖circleMap 0 (1 - ρ) t₁ - circleMap 0 (1 - ρ) t₂‖ := hmvt
    _ ≤ C₀ * ρ ^ (-1 + α) * ρ := by
        apply mul_le_mul_of_nonneg_left hlip_bound
        exact mul_nonneg hC₀ (Real.rpow_nonneg (le_of_lt hρ_pos) _)
    _ = C₀ * ρ ^ α := by
        have : ρ ^ (-1 + α) * ρ ^ (1 : ℝ) = ρ ^ (-1 + α + 1) :=
          (Real.rpow_add hρ_pos (-1 + α) 1).symm
        rw [Real.rpow_one] at this
        rw [mul_assoc, this]
        congr 1
        ring_nf

lemma hasDerivAt_circleMap_sub (t s : ℝ) :
    HasDerivAt (fun s => circleMap (0 : ℂ) (1 - s) t) (-circleMap 0 1 t) s := by
  simp_rw [circleMap_zero]
  have hd : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1 : ℝ) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℝ)
  have := (hd.ofReal_comp).mul_const (Complex.exp (↑t * Complex.I))
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul] at this ⊢
  exact this

theorem radial_segment_bound
    (F : ℂ → ℂ) (C₀ : ℝ) (α : ℝ) (t : ℝ)
    (hC₀ : 0 ≤ C₀)
    (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (hcont : ContinuousOn F (Metric.closedBall 0 1))
    (hdiff : DifferentiableOn ℝ F (Metric.ball 0 1))
    (hgrad : SatisfiesGradientBound F C₀ α)
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ 1) :
    ‖F (circleMap 0 1 t) - F (circleMap 0 (1 - ρ) t)‖ ≤ C₀ / α * ρ ^ α := by
  set g : ℝ → ℂ := fun s => F (circleMap 0 (1 - s) t) with hg_def
  have hg0 : g 0 = F (circleMap 0 1 t) := by simp [g, sub_zero]
  have hgρ : g ρ = F (circleMap 0 (1 - ρ) t) := rfl
  rw [← hg0, ← hgρ]
  have hg_cont : ContinuousOn g (Icc 0 1) := by
    apply hcont.comp (Continuous.continuousOn (by simp_rw [circleMap_zero]; fun_prop))
    intro s hs; simp only [mem_Icc] at hs
    simp only [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - s by linarith)]
    linarith
  have hg_hasDerivAt : ∀ x : ℝ, 0 < x → x ≤ 1 →
      HasDerivAt g (fderiv ℝ F (circleMap 0 (1 - x) t) (-circleMap 0 1 t)) x := by
    intro x hx hx1
    have h_in : circleMap 0 (1 - x) t ∈ Metric.ball (0 : ℂ) 1 := by
      simp only [Metric.mem_ball, dist_zero_right, norm_circleMap_zero,
        abs_of_nonneg (show (0 : ℝ) ≤ 1 - x by linarith)]
      linarith
    exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds h_in)).hasFDerivAt.comp_hasDerivAt
      x (hasDerivAt_circleMap_sub t x)
  have hg_deriv_bound : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ‖fderiv ℝ F (circleMap 0 (1 - s) t) (-circleMap 0 1 t)‖ ≤ C₀ * s ^ (-1 + α) := by
    intro s hs hs1
    have h_in : ‖circleMap 0 (1 - s) t‖ < 1 := by
      rw [norm_circleMap_zero, abs_of_nonneg (show (0 : ℝ) ≤ 1 - s by linarith)]; linarith
    have h_op := (fderiv ℝ F (circleMap 0 (1 - s) t)).le_opNorm (-circleMap 0 1 t)
    rw [norm_neg, norm_circleMap_zero, abs_one, mul_one] at h_op
    have h_grad := hgrad _ h_in
    rw [norm_circleMap_zero, abs_of_nonneg (show (0 : ℝ) ≤ 1 - s by linarith),
      show 1 - (1 - s) = s from by ring] at h_grad
    exact le_trans h_op h_grad
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hg_cwa : ContinuousWithinAt g (Icc 0 1) 0 :=
    hg_cont 0 (left_mem_Icc.mpr (by linarith : (0 : ℝ) ≤ 1))
  rw [Metric.continuousWithinAt_iff] at hg_cwa
  obtain ⟨η, hη_pos, hη⟩ := hg_cwa δ hδ
  set ε := min (η / 2) (ρ / 2) with hε_def
  have hε_pos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε_le_ρ : ε ≤ ρ := (min_le_right _ _).trans (by linarith)
  have hε_le_1 : ε ≤ 1 := hε_le_ρ.trans hρ_le
  have hg_close : dist (g 0) (g ε) < δ := by
    rw [dist_comm]
    apply hη
    · exact ⟨le_of_lt hε_pos, hε_le_1⟩
    · simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htri : ‖g 0 - g ρ‖ ≤ ‖g 0 - g ε‖ + ‖g ε - g ρ‖ := by
    calc ‖g 0 - g ρ‖ = ‖(g 0 - g ε) + (g ε - g ρ)‖ := by ring_nf
      _ ≤ ‖g 0 - g ε‖ + ‖g ε - g ρ‖ := norm_add_le _ _
  have h1 : ‖g 0 - g ε‖ < δ := by rw [← dist_eq_norm]; exact hg_close
  have h2 : ‖g ε - g ρ‖ ≤ C₀ / α * ρ ^ α := by
    have hg_diff : ∀ x ∈ uIcc ε ρ, DifferentiableAt ℝ g x := by
      intro x hx; simp only [uIcc_of_le hε_le_ρ, mem_Icc] at hx
      exact (hg_hasDerivAt x (by linarith) (by linarith)).differentiableAt
    have hbd : ∀ s ∈ Ioc ε ρ, ‖deriv g s‖ ≤ C₀ * ε ^ (-1 + α) := by
      intro s hs; simp only [mem_Ioc] at hs
      rw [(hg_hasDerivAt s (by linarith) (by linarith)).deriv]
      calc ‖fderiv ℝ F (circleMap 0 (1 - s) t) (-circleMap 0 1 t)‖
          ≤ C₀ * s ^ (-1 + α) := hg_deriv_bound s (by linarith) (by linarith)
        _ ≤ C₀ * ε ^ (-1 + α) := by
            apply mul_le_mul_of_nonneg_left _ hC₀
            exact Real.rpow_le_rpow_of_nonpos hε_pos (le_of_lt hs.1) (by linarith)
    have hint : IntervalIntegrable (deriv g) volume ε ρ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε_le_ρ]
      exact Measure.integrableOn_of_bounded (M := C₀ * ε ^ (-1 + α))
        measure_Ioc_lt_top.ne (measurable_deriv g).aestronglyMeasurable
        (Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioc) hbd)
    have hftc : ∫ s in ε..ρ, deriv g s = g ρ - g ε :=
      intervalIntegral.integral_deriv_eq_sub hg_diff hint
    rw [norm_sub_rev]
    rw [← hftc]
    calc ‖∫ s in ε..ρ, deriv g s‖
        ≤ ∫ s in ε..ρ, ‖deriv g s‖ :=
          intervalIntegral.norm_integral_le_integral_norm hε_le_ρ
      _ ≤ ∫ s in ε..ρ, C₀ * s ^ (-1 + α) := by
          apply intervalIntegral.integral_mono_on hε_le_ρ
          · exact hint.norm
          · exact (intervalIntegral.intervalIntegrable_rpow'
              (by linarith : (-1 : ℝ) < -1 + α)).const_mul C₀
          · intro s hs; simp only [mem_Icc] at hs
            rw [(hg_hasDerivAt s (by linarith) (by linarith)).deriv]
            exact hg_deriv_bound s (by linarith) (by linarith)
      _ = C₀ * (ρ ^ α - ε ^ α) / α := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -1 + α))]
          ring_nf
      _ ≤ C₀ / α * ρ ^ α := by
          have hε_rpow : 0 ≤ ε ^ α := Real.rpow_nonneg (le_of_lt hε_pos) α
          have hρ_rpow : 0 ≤ ρ ^ α := Real.rpow_nonneg (le_of_lt hρ_pos) α
          rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ (le_of_lt hα_pos)
          nlinarith
  linarith

theorem holder_boundary_of_gradient_bound
    (F : ℂ → ℂ) (C : ℝ) (α : ℝ)
    (hC : 0 < C)
    (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (hcont : ContinuousOn F (Metric.closedBall 0 1))
    (hdiff : DifferentiableOn ℝ F (Metric.ball 0 1))
    (hgrad : SatisfiesGradientBound F C α) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ t₁ t₂ : ℝ,
      ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤ C' * |t₁ - t₂| ^ α := by
  refine ⟨2 * C / α + C, by positivity, fun t₁ t₂ => ?_⟩
  have hC_nn : (0 : ℝ) ≤ C := le_of_lt hC
  by_cases ht_eq : t₁ = t₂
  · rw [ht_eq, sub_self, norm_zero]; positivity
  · have hρ_pos : 0 < |t₁ - t₂| := abs_pos.mpr (sub_ne_zero.mpr ht_eq)
    by_cases hρ_le : |t₁ - t₂| ≤ 1
    · have hL1 := radial_segment_bound F C α t₁ hC_nn hα_pos hα_le hcont hdiff hgrad
          |t₁ - t₂| hρ_pos hρ_le
      have hL3 := radial_segment_bound F C α t₂ hC_nn hα_pos hα_le hcont hdiff hgrad
          |t₁ - t₂| hρ_pos hρ_le
      have hL2 := arc_segment_bound F C α |t₁ - t₂| t₁ t₂ hC_nn hα_pos hα_le
          hρ_pos hρ_le hdiff hgrad le_rfl
      have htri : ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤
          ‖F (circleMap 0 1 t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₁)‖ +
          ‖F (circleMap 0 (1 - |t₁ - t₂|) t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)‖ +
          ‖F (circleMap 0 1 t₂) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)‖ := by
        have heq : F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂) =
          (F (circleMap 0 1 t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₁)) +
          (F (circleMap 0 (1 - |t₁ - t₂|) t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)) +
          (F (circleMap 0 (1 - |t₁ - t₂|) t₂) - F (circleMap 0 1 t₂)) := by ring
        rw [heq]
        linarith [norm_add_le
          ((F (circleMap 0 1 t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₁)) +
           (F (circleMap 0 (1 - |t₁ - t₂|) t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)))
          (F (circleMap 0 (1 - |t₁ - t₂|) t₂) - F (circleMap 0 1 t₂)),
          norm_add_le
          (F (circleMap 0 1 t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₁))
          (F (circleMap 0 (1 - |t₁ - t₂|) t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)),
          norm_sub_rev
          (F (circleMap 0 (1 - |t₁ - t₂|) t₂)) (F (circleMap 0 1 t₂))]
      have hsum : C / α * |t₁ - t₂| ^ α + C * |t₁ - t₂| ^ α + C / α * |t₁ - t₂| ^ α
          = (2 * C / α + C) * |t₁ - t₂| ^ α := by ring
      linarith [hsum]
    · push Not at hρ_le
      have hL1 := radial_segment_bound F C α t₁ hC_nn hα_pos hα_le hcont hdiff hgrad
          1 one_pos le_rfl
      have hL3 := radial_segment_bound F C α t₂ hC_nn hα_pos hα_le hcont hdiff hgrad
          1 one_pos le_rfl
      rw [show (1 : ℝ) - 1 = 0 from sub_self 1] at hL1 hL3
      rw [show ∀ t : ℝ, circleMap (0 : ℂ) 0 t = 0 from
          fun t => by simp [circleMap_zero]] at hL1 hL3
      rw [Real.one_rpow] at hL1 hL3
      have htri : ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤
          ‖F (circleMap 0 1 t₁) - F 0‖ + ‖F (circleMap 0 1 t₂) - F 0‖ := by
        have heq : F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂) =
          (F (circleMap 0 1 t₁) - F 0) + (F 0 - F (circleMap 0 1 t₂)) := by ring
        rw [heq]
        linarith [norm_add_le (F (circleMap 0 1 t₁) - F 0) (F 0 - F (circleMap 0 1 t₂)),
                  norm_sub_rev (F 0) (F (circleMap 0 1 t₂))]
      have hρα_ge_1 : 1 ≤ |t₁ - t₂| ^ α :=
        Real.one_le_rpow (le_of_lt hρ_le) (le_of_lt hα_pos)
      have hbound : ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤ C / α * 1 + C / α * 1 :=
        by linarith
      have heq : C / α * 1 + C / α * 1 = 2 * C / α := by ring
      calc ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖
          ≤ 2 * C / α + C := by linarith [hbound, heq]
        _ = (2 * C / α + C) * 1 := by ring
        _ ≤ (2 * C / α + C) * |t₁ - t₂| ^ α := by
            apply mul_le_mul_of_nonneg_left hρα_ge_1; positivity

/-- **Hölder boundary values.** If `F : ℂ → ℂ` is continuous on the closed unit disc,
real-differentiable on the open disc, and `‖fderiv ℝ F z‖ ≤ C (1 - ‖z‖)^(α - 1)` for `‖z‖ < 1`,
with `0 < α ≤ 1`, then `t ↦ F (circleMap 0 1 t)` is `α`-Hölder. -/
public theorem holderWith_circleMap_of_norm_fderiv_le {F : ℂ → ℂ} {C : ℝ} {α : ℝ≥0}
    (hC : 0 < C) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (hcont : ContinuousOn F (Metric.closedBall 0 1))
    (hdiff : DifferentiableOn ℝ F (Metric.ball 0 1))
    (hgrad : ∀ z : ℂ, ‖z‖ < 1 → ‖fderiv ℝ F z‖ ≤ C * (1 - ‖z‖) ^ ((α : ℝ) - 1)) :
    ∃ C' : ℝ≥0, HolderWith C' α fun t : ℝ => F (circleMap 0 1 t) := by
  obtain ⟨C', hC', hbound⟩ := holder_boundary_of_gradient_bound F C α hC hα_pos hα_le hcont
    hdiff fun z hz => by simpa [neg_add_eq_sub] using hgrad z hz
  refine ⟨⟨C', hC'.le⟩, fun t₁ t₂ => ?_⟩
  rw [edist_dist, edist_dist]
  calc ENNReal.ofReal (dist (F (circleMap 0 1 t₁)) (F (circleMap 0 1 t₂)))
      ≤ ENNReal.ofReal (C' * dist t₁ t₂ ^ (α : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by simpa [dist_eq_norm, Real.dist_eq] using hbound t₁ t₂)
    _ = _ := by
        rw [ENNReal.ofReal_mul hC'.le, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]
        congr 1
        exact ENNReal.ofReal_eq_coe_nnreal hC'.le

end Complex
