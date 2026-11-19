/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Circle averages of a harmonic function on an annulus

If `u` is harmonic on the closed annulus `r₁ ≤ ‖z - z₀‖ ≤ r₂` with `0 < r₁`, then its circle
average is `α log r + β` there
(`InnerProductSpace.HarmonicOnNhd.exists_circleAverage_eq_mul_log_add`).

Differentiating under the integral sign twice, the circle average `V r` satisfies Euler's
equation `r² V'' + r V' = 0` (the Laplacian in polar coordinates averaged over the circle), so
`r V'` is constant and `V = α log r + β`. Mathlib has the mean value property on discs
(`HarmonicOnNhd.circleAverage_eq`) but not the annulus statement.

Code-derived port of `harmonic_annulus_mean_value` and its helpers from
`v1/Atlas/ComplexVariables/code/Lecture16.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 1026–1585 (Theorem 20), with the archived
`IsHarmonic` abbreviation of `HarmonicOnNhd` kept private. The public statement asks for `u`
harmonic on the closed annulus itself, instead of on an open set containing it; Mathlib's
`isOpen_setOfPred_harmonicAt` supplies the open set. The archived formalization and its original
license/provenance remain in `v1/` (the original license text is `v1/LICENSE`). This records
equivalence to the archived Lean statement, not verification against the printed textbook.
-/

set_option autoImplicit false

open Complex InnerProductSpace Laplacian Metric Real Set Topology Filter MeasureTheory

namespace InnerProductSpace

abbrev IsHarmonic (u : ℂ → ℝ) (Ω : Set ℂ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u Ω

lemma IsHarmonic.contDiffOn {u : ℂ → ℝ} {Ω : Set ℂ} (hu : IsHarmonic u Ω) :
    ContDiffOn ℝ 2 u Ω :=
  HarmonicOnNhd.contDiffOn hu

lemma IsHarmonic.harmonicAt {u : ℂ → ℝ} {Ω : Set ℂ} (hu : IsHarmonic u Ω)
    {z : ℂ} (hz : z ∈ Ω) : HarmonicAt u z :=
  hu z hz

lemma IsHarmonic.mono {u : ℂ → ℝ} {Ω₁ Ω₂ : Set ℂ} (hu : IsHarmonic u Ω₁) (h : Ω₂ ⊆ Ω₁) :
    IsHarmonic u Ω₂ :=
  HarmonicOnNhd.mono hu h

theorem circleAverage_hasDerivAt_first
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ r₀ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (_hr₁₂ : r₁ ≤ r₂) (hr0 : r₁ ≤ r₀) (hr0' : r₀ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    HasDerivAt (fun s => circleAverage u z₀ s)
      ((2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ u (circleMap z₀ r₀ θ)) (exp (↑θ * I))) r₀ := by
  change HasDerivAt (fun s => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, u (circleMap z₀ s θ)) _ r₀
  suffices h : HasDerivAt (fun s => ∫ θ in (0 : ℝ)..2 * π, u (circleMap z₀ s θ))
      (∫ θ in (0 : ℝ)..2 * π, (fderiv ℝ u (circleMap z₀ r₀ θ)) (exp (↑θ * I))) r₀ by
    exact h.const_smul (2 * π)⁻¹
  set K := {z : ℂ | r₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r₂}
  have hK_compact : IsCompact K := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall z₀ r₂)
    · exact (isClosed_le continuous_const
        (continuous_norm.comp (continuous_id.sub continuous_const))).inter
        (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
    · intro z ⟨_, h2⟩; exact mem_closedBall.mpr (by rwa [dist_comm, dist_eq_norm, norm_sub_rev])
  have hK_sub : K ⊆ Ω := fun z ⟨h1, h2⟩ => hannulus z h1 h2
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hK_compact.exists_thickening_subset_open hΩ hK_sub
  have hr0_pos : 0 < r₀ := lt_of_lt_of_le hr₁ hr0
  have hmem_K : ∀ θ, circleMap z₀ r₀ θ ∈ K := fun θ =>
    ⟨by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0_pos]; exact hr0,
     by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0_pos]; exact hr0'⟩
  have hK2_sub_Ω : cthickening (δ / 2) K ⊆ Ω :=
    (cthickening_subset_thickening' hδ_pos (by linarith) K).trans hδ_sub
  have hmem_cthick : ∀ x ∈ ball r₀ (δ / 2), ∀ θ,
      circleMap z₀ x θ ∈ cthickening (δ / 2) K := by
    intro x hx θ
    apply mem_cthickening_of_dist_le _ (circleMap z₀ r₀ θ) _ _ (hmem_K θ)
    simp only [circleMap, dist_eq_norm]
    rw [show z₀ + ↑x * exp (↑θ * I) - (z₀ + ↑r₀ * exp (↑θ * I)) =
      (↑x - ↑r₀) * exp (↑θ * I) by ring,
      Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact le_of_lt (by rwa [mem_ball, Real.dist_eq] at hx)
  have hmem_Ω : ∀ x ∈ ball r₀ (δ / 2), ∀ θ, circleMap z₀ x θ ∈ Ω := fun x hx θ =>
    hK2_sub_Ω (hmem_cthick x hx θ)
  have hu_C2 : ContDiffOn ℝ 2 u Ω := hu.contDiffOn
  have hu_cont : ContinuousOn u Ω := hu_C2.continuousOn
  have hfderiv_cont : ContinuousOn (fderiv ℝ u) Ω :=
    hu_C2.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
  have hu_diff : ∀ z ∈ Ω, DifferentiableAt ℝ u z := fun z hz =>
    (hu_C2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (hΩ.mem_nhds hz)
  obtain ⟨M, hM⟩ := (hK_compact.cthickening (r := δ / 2)).exists_bound_of_continuousOn
    (hfderiv_cont.mono hK2_sub_Ω)
  have leibniz := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (a := 0) (b := 2 * π) (μ := MeasureTheory.MeasureSpace.volume)
    (bound := fun _ => M)
    (F := fun s θ => u (circleMap z₀ s θ))
    (F' := fun s θ => (fderiv ℝ u (circleMap z₀ s θ)) (exp (↑θ * I)))
    (x₀ := r₀) (s := ball r₀ (δ / 2))
    (ball_mem_nhds r₀ (by linarith))
    (by apply eventually_of_mem (ball_mem_nhds r₀ (by linarith : δ / 2 > 0))
        intro x hx
        exact (hu_cont.comp_continuous (continuous_circleMap z₀ x)
          (hmem_Ω x hx)).aestronglyMeasurable)
    ((hu_cont.comp_continuous (continuous_circleMap z₀ r₀)
      (fun θ => hK_sub (hmem_K θ))).intervalIntegrable 0 _)
    (by have h1 : Continuous (fun θ => fderiv ℝ u (circleMap z₀ r₀ θ)) :=
          hfderiv_cont.comp_continuous (continuous_circleMap z₀ r₀) (fun θ => hK_sub (hmem_K θ))
        have h2 : Continuous (fun θ : ℝ => exp ((θ : ℂ) * I)) := by fun_prop
        exact ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp
          (h1.prodMk h2)).aestronglyMeasurable)
    (by apply Eventually.of_forall; intro t _ x hx
        calc ‖(fderiv ℝ u (circleMap z₀ x t)) (exp (↑t * I))‖
            ≤ ‖fderiv ℝ u (circleMap z₀ x t)‖ * ‖exp (↑t * I)‖ :=
              (fderiv ℝ u (circleMap z₀ x t)).le_opNorm _
          _ = ‖fderiv ℝ u (circleMap z₀ x t)‖ := by
              rw [Complex.norm_exp_ofReal_mul_I, mul_one]
          _ ≤ M := hM _ (hmem_cthick x hx t))
    intervalIntegrable_const
    (by apply Eventually.of_forall; intro t _ x hx
        exact (hu_diff _ (hmem_Ω x hx t)).hasFDerivAt.comp_hasDerivAt x (by
          have : HasDerivAt (fun R : ℝ => z₀ + (R : ℂ) * exp (↑t * I))
              (exp (↑t * I)) x := by
            simpa using (Complex.ofRealCLM.hasDerivAt.mul_const
              (exp (↑t * I))).const_add z₀
          convert this using 1
          funext R
          simp [circleMap]))
  exact leibniz.2

theorem circleAverage_hasDerivAt_second
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ r₀ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (_hr₁₂ : r₁ ≤ r₂) (hr0 : r₁ ≤ r₀) (hr0' : r₀ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    let V' := fun r => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ u (circleMap z₀ r θ)) (exp (↑θ * I))
    HasDerivAt V'
      ((2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ))
          (exp (↑θ * I))) r₀ := by
  intro V'
  suffices h : HasDerivAt (fun s => ∫ θ in (0 : ℝ)..2 * π,
      (fderiv ℝ u (circleMap z₀ s θ)) (exp (↑θ * I)))
      (∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ))
          (exp (↑θ * I))) r₀ by
    exact h.const_smul (2 * π)⁻¹
  set K := {z : ℂ | r₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r₂}
  have hK_compact : IsCompact K := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall z₀ r₂)
    · exact (isClosed_le continuous_const
        (continuous_norm.comp (continuous_id.sub continuous_const))).inter
        (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
    · intro z ⟨_, h2⟩; exact mem_closedBall.mpr (by rwa [dist_comm, dist_eq_norm, norm_sub_rev])
  have hK_sub : K ⊆ Ω := fun z ⟨h1, h2⟩ => hannulus z h1 h2
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hK_compact.exists_thickening_subset_open hΩ hK_sub
  have hr0_pos : 0 < r₀ := lt_of_lt_of_le hr₁ hr0
  have hmem_K : ∀ θ, circleMap z₀ r₀ θ ∈ K := fun θ =>
    ⟨by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0_pos]; exact hr0,
     by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0_pos]; exact hr0'⟩
  have hK2_sub_Ω : cthickening (δ / 2) K ⊆ Ω :=
    (cthickening_subset_thickening' hδ_pos (by linarith) K).trans hδ_sub
  have hmem_cthick : ∀ x ∈ ball r₀ (δ / 2), ∀ θ,
      circleMap z₀ x θ ∈ cthickening (δ / 2) K := by
    intro x hx θ
    apply mem_cthickening_of_dist_le _ (circleMap z₀ r₀ θ) _ _ (hmem_K θ)
    simp only [circleMap, dist_eq_norm]
    rw [show z₀ + ↑x * exp (↑θ * I) - (z₀ + ↑r₀ * exp (↑θ * I)) =
      (↑x - ↑r₀) * exp (↑θ * I) by ring,
      Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact le_of_lt (by rwa [mem_ball, Real.dist_eq] at hx)
  have hmem_Ω : ∀ x ∈ ball r₀ (δ / 2), ∀ θ, circleMap z₀ x θ ∈ Ω := fun x hx θ =>
    hK2_sub_Ω (hmem_cthick x hx θ)
  have hu_C2 : ContDiffOn ℝ 2 u Ω := hu.contDiffOn
  have hfderiv_cont : ContinuousOn (fderiv ℝ u) Ω :=
    hu_C2.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
  have hfderiv_C1 : ContDiffOn ℝ 1 (fderiv ℝ u) Ω :=
    hu_C2.fderiv_of_isOpen hΩ (by norm_num)
  have hfderiv2_cont : ContinuousOn (fderiv ℝ (fderiv ℝ u)) Ω :=
    hfderiv_C1.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
  have hg_diff : ∀ z ∈ Ω, ∀ v : ℂ, DifferentiableAt ℝ (fun w => (fderiv ℝ u w) v) z :=
    fun z hz v =>
      ((ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp_contDiffOn hfderiv_C1).differentiableOn
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt (hΩ.mem_nhds hz)
  obtain ⟨M, hM⟩ := (hK_compact.cthickening (r := δ / 2)).exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ u)) (hfderiv2_cont.mono hK2_sub_Ω)
  have leibniz := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (a := 0) (b := 2 * π) (μ := MeasureTheory.MeasureSpace.volume)
    (bound := fun _ => M)
    (F := fun s θ => (fderiv ℝ u (circleMap z₀ s θ)) (exp (↑θ * I)))
    (F' := fun s θ => (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I)))
        (circleMap z₀ s θ)) (exp (↑θ * I)))
    (x₀ := r₀) (s := ball r₀ (δ / 2))
    (ball_mem_nhds r₀ (by linarith))
    (by apply eventually_of_mem (ball_mem_nhds r₀ (by linarith : δ / 2 > 0))
        intro x hx
        have h1 : Continuous (fun θ => fderiv ℝ u (circleMap z₀ x θ)) :=
          hfderiv_cont.comp_continuous (continuous_circleMap z₀ x) (fun θ => hmem_Ω x hx θ)
        have h2 : Continuous (fun θ : ℝ => exp ((θ : ℂ) * I)) := by fun_prop
        exact ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp
          (h1.prodMk h2)).aestronglyMeasurable)
    (by have h1 : Continuous (fun θ => fderiv ℝ u (circleMap z₀ r₀ θ)) :=
          hfderiv_cont.comp_continuous (continuous_circleMap z₀ r₀) (fun θ => hK_sub (hmem_K θ))
        have h2 : Continuous (fun θ : ℝ => exp ((θ : ℂ) * I)) := by fun_prop
        exact ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp
          (h1.prodMk h2)).intervalIntegrable 0 _)
    (by
        have hfdu_diff_at : ∀ z ∈ Ω, DifferentiableAt ℝ (fderiv ℝ u) z := fun z hz =>
          (hfderiv_C1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
            (hΩ.mem_nhds hz)
        suffices Continuous (fun θ => (fderiv ℝ (fun z => (fderiv ℝ u z)
            (exp (↑θ * I))) (circleMap z₀ r₀ θ)) (exp (↑θ * I))) by
          exact this.aestronglyMeasurable
        have hrewrite : ∀ θ, fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I)))
            (circleMap z₀ r₀ θ) =
            (ContinuousLinearMap.apply ℝ ℝ (exp (↑θ * I))).comp
              (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) := by
          intro θ
          exact ((ContinuousLinearMap.apply ℝ ℝ (exp (↑θ * I))).hasFDerivAt.comp
            (circleMap z₀ r₀ θ) (hfdu_diff_at _ (hK_sub (hmem_K θ))).hasFDerivAt).fderiv
        simp_rw [hrewrite, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
        have hA : Continuous (fun θ => fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) :=
          hfderiv2_cont.comp_continuous (continuous_circleMap z₀ r₀) (fun θ => hK_sub (hmem_K θ))
        have hB : Continuous (fun θ : ℝ => exp ((θ : ℂ) * I)) := by fun_prop
        exact (((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp
          (((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp (hA.prodMk hB)).prodMk hB))))
    (by apply Eventually.of_forall; intro t _ x hx
        change ‖(fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑t * I))) (circleMap z₀ x t))
            (exp (↑t * I))‖ ≤ M
        have hfdu_diff_at : DifferentiableAt ℝ (fderiv ℝ u) (circleMap z₀ x t) :=
          (hfderiv_C1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
            (hΩ.mem_nhds (hmem_Ω x hx t))
        have hkey : HasFDerivAt (fun z => (fderiv ℝ u z) (exp (↑t * I)))
            ((ContinuousLinearMap.apply ℝ ℝ (exp (↑t * I))).comp
              (fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t))) (circleMap z₀ x t) := by
          change HasFDerivAt ((fun g => g (exp (↑t * I))) ∘ fderiv ℝ u) _ _
          exact (ContinuousLinearMap.apply ℝ ℝ (exp (↑t * I))).hasFDerivAt.comp
            (circleMap z₀ x t) hfdu_diff_at.hasFDerivAt
        rw [hkey.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
        calc ‖(fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)) (exp (↑t * I)) (exp (↑t * I))‖
            ≤ ‖(fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)) (exp (↑t * I))‖ *
              ‖exp (↑t * I)‖ :=
              ((fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)) (exp (↑t * I))).le_opNorm _
          _ = ‖(fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)) (exp (↑t * I))‖ := by
              rw [Complex.norm_exp_ofReal_mul_I, mul_one]
          _ ≤ ‖fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)‖ * ‖exp (↑t * I)‖ :=
              (fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)).le_opNorm _
          _ = ‖fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)‖ := by
              rw [Complex.norm_exp_ofReal_mul_I, mul_one]
          _ ≤ M := hM _ (hmem_cthick x hx t))
    intervalIntegrable_const
    (by apply Eventually.of_forall; intro t _ x hx
        exact (hg_diff _ (hmem_Ω x hx t) (exp (↑t * I))).hasFDerivAt.comp_hasDerivAt x (by
          have : HasDerivAt (fun R : ℝ => z₀ + (R : ℂ) * exp (↑t * I))
              (exp (↑t * I)) x := by
            simpa using (Complex.ofRealCLM.hasDerivAt.mul_const
              (exp (↑t * I))).const_add z₀
          convert this using 1))
  exact leibniz.2

lemma bilinear_trace_rotation (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (z : ℂ) :
    B z z + B (I * z) (I * z) = (z.re ^ 2 + z.im ^ 2) * (B 1 1 + B I I) := by
  set a := z.re; set b := z.im
  have hz : z = (a : ℝ) • (1 : ℂ) + (b : ℝ) • (I : ℂ) := by
    apply Complex.ext <;> simp [a, b]
  have hiz : I * z = (-(b : ℝ)) • (1 : ℂ) + (a : ℝ) • (I : ℂ) := by
    apply Complex.ext <;> simp [a, b, mul_comm]
  conv_lhs =>
    rw [hz]
    rw [show I * ((a : ℝ) • (1 : ℂ) + (b : ℝ) • (I : ℂ)) =
        (-(b : ℝ)) • (1 : ℂ) + (a : ℝ) • (I : ℂ) from by rw [← hz]; exact hiz]
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  simp; ring

lemma harmonic_fderiv_trace_zero {u : ℂ → ℝ} {z : ℂ} (h : HarmonicAt u z) :
    (fderiv ℝ (fderiv ℝ u) z) 1 1 + (fderiv ℝ (fderiv ℝ u) z) I I = 0 := by
  have hΔ : (Laplacian.laplacian u) z = 0 := h.2.eq_of_nhds
  have hformula := laplacian_eq_iteratedFDeriv_orthonormalBasis u Complex.orthonormalBasisOneI
  rw [hformula] at hΔ
  simp only [Fin.sum_univ_two] at hΔ
  have hv0 : (Complex.orthonormalBasisOneI : Fin 2 → ℂ) 0 = 1 :=
    by simp [show (Complex.orthonormalBasisOneI : Fin 2 → ℂ) 0 = (![1, I] : Fin 2 → ℂ) 0 from
      congr_fun Complex.coe_orthonormalBasisOneI 0]
  have hv1 : (Complex.orthonormalBasisOneI : Fin 2 → ℂ) 1 = I :=
    by simp [show (Complex.orthonormalBasisOneI : Fin 2 → ℂ) 1 = (![1, I] : Fin 2 → ℂ) 1 from
      congr_fun Complex.coe_orthonormalBasisOneI 1]
  rw [hv0, hv1] at hΔ
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    ← bilinearIteratedFDerivTwo_eq_iteratedFDeriv] at hΔ
  exact hΔ

lemma harmonic_second_deriv_neg {u : ℂ → ℝ} {z e : ℂ} (h : HarmonicAt u z)
    (he : e.re ^ 2 + e.im ^ 2 = 1) :
    (fderiv ℝ (fderiv ℝ u) z) e e = -(fderiv ℝ (fderiv ℝ u) z) (I * e) (I * e) := by
  have := bilinear_trace_rotation (fderiv ℝ (fderiv ℝ u) z) e
  rw [he, one_mul] at this
  linarith [this, harmonic_fderiv_trace_zero h]

lemma cexp_re_sq_add_im_sq (θ : ℝ) :
    (cexp (↑θ * I)).re ^ 2 + (cexp (↑θ * I)).im ^ 2 = 1 := by
  rw [exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]

theorem periodicity_of_circle_derivative
    {u : ℂ → ℝ} {z₀ : ℂ} {r₀ : ℝ}
    (hu_C2 : ∀ θ : ℝ, ContDiffAt ℝ 2 u (circleMap z₀ r₀ θ)) :
    r₀ * ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * exp (↑θ * I)) (I * exp (↑θ * I)) =
      ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ u (circleMap z₀ r₀ θ)) (exp (↑θ * I)) := by
  have hDu_cont : Continuous (fun (t : ℝ) => fderiv ℝ u (circleMap z₀ r₀ t)) := by
    apply continuous_iff_continuousAt.mpr; intro t
    exact ((hu_C2 t).fderiv_right (m := 1) le_rfl).continuousAt.comp
      (continuous_circleMap z₀ r₀).continuousAt
  have hD2u_cont : Continuous (fun (t : ℝ) => fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ t)) := by
    apply continuous_iff_continuousAt.mpr; intro t
    exact ((hu_C2 t).fderiv_right (m := 1) le_rfl |>.fderiv_right (m := 0)
      le_rfl).continuousAt.comp (continuous_circleMap z₀ r₀).continuousAt
  have hIexp_cont : Continuous (fun (t : ℝ) => I * exp ((↑t : ℂ) * I)) := by fun_prop
  have hexp_cont : Continuous (fun (t : ℝ) => exp ((↑t : ℂ) * I)) := by fun_prop
  have hA_int : IntervalIntegrable (fun (t : ℝ) =>
      r₀ * (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ t)) (I * exp (↑t * I)) (I * exp (↑t * I)))
      volume 0 (2 * π) :=
    (((hD2u_cont.clm_apply hIexp_cont).clm_apply hIexp_cont).const_mul r₀).intervalIntegrable 0 _
  have hB_int : IntervalIntegrable (fun (t : ℝ) =>
      (fderiv ℝ u (circleMap z₀ r₀ t)) (exp (↑t * I))) volume 0 (2 * π) :=
    (hDu_cont.clm_apply hexp_cont).intervalIntegrable 0 _
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * π), HasDerivAt
      (fun (s : ℝ) => (fderiv ℝ u (circleMap z₀ r₀ s)) (I * exp (↑s * I)))
      (r₀ * (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ t)) (I * exp (↑t * I)) (I * exp (↑t * I))
       - (fderiv ℝ u (circleMap z₀ r₀ t)) (exp (↑t * I))) t := by
    intro t _
    have hDu_diff : DifferentiableAt ℝ (fderiv ℝ u) (circleMap z₀ r₀ t) :=
      ((hu_C2 t).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
    have hcircle := hasDerivAt_circleMap z₀ r₀ t
    have hc : HasDerivAt (fun (s : ℝ) => fderiv ℝ u (circleMap z₀ r₀ s))
        ((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ t)) (circleMap 0 r₀ t * I)) t :=
      hDu_diff.hasFDerivAt.comp_hasDerivAt t hcircle
    have he : HasDerivAt (fun (s : ℝ) => exp ((↑s : ℂ) * I)) (exp ((↑t : ℂ) * I) * I) t := by
      have h1 := ((ofRealCLM.hasDerivAt (x := t)).mul_const I).cexp
      simp only [ofRealCLM_apply, ofReal_one, one_mul] at h1; exact h1
    have hv : HasDerivAt (fun (s : ℝ) => I * exp ((↑s : ℂ) * I))
        (I * (exp ((↑t : ℂ) * I) * I)) t := he.const_mul I
    refine (hc.clm_apply hv).congr_deriv ?_
    set e := exp ((↑t : ℂ) * I)
    have h1 : circleMap 0 r₀ t * I = r₀ • (I * e) := by
      rw [circleMap_zero, Complex.real_smul]; ring
    rw [h1]; simp only [map_smul, smul_apply, smul_eq_mul]
    have h3 : I * (e * I) = (-1 : ℝ) • e := by
      simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_one]
      ring_nf; rw [I_sq]; ring
    rw [h3, map_smul, smul_eq_mul]; ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hA_int.sub hB_int)
  have hper : (fderiv ℝ u (circleMap z₀ r₀ (2 * π))) (I * exp (↑(2 * π) * I)) =
      (fderiv ℝ u (circleMap z₀ r₀ 0)) (I * exp (↑(0 : ℝ) * I)) := by
    have hcm : circleMap z₀ r₀ (2 * π) = circleMap z₀ r₀ 0 := by
      simpa using periodic_circleMap z₀ r₀ 0
    have hexp : exp ((↑(2 * π) : ℂ) * I) = exp ((↑(0 : ℝ) : ℂ) * I) := by
      have h := exp_mul_I_periodic (0 : ℂ)
      simp only [zero_add, ofReal_zero, zero_mul, Complex.exp_zero] at h ⊢
      push_cast; exact h
    rw [hcm, hexp]
  rw [hper, sub_self] at hftc
  rw [intervalIntegral.integral_sub hA_int hB_int] at hftc
  rw [intervalIntegral.integral_const_mul] at hftc
  linarith

lemma fderiv_eval_eq_fderiv2 {u : ℂ → ℝ} {z₀ v w : ℂ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) z₀) :
    (fderiv ℝ (fun z => (fderiv ℝ u z) v) z₀) w =
    (fderiv ℝ (fderiv ℝ u) z₀) w v := by
  have hL : HasFDerivAt (fun z => (fderiv ℝ u z) v)
    ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ u) z₀)) z₀ :=
    ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp z₀ hu.hasFDerivAt
  rw [hL.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

theorem euler_ode_from_laplacian
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ r₀ : ℝ}
    (hu : IsHarmonic u Ω) (_hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (_hr₁₂ : r₁ ≤ r₂) (hr0 : r₁ ≤ r₀) (hr0' : r₀ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    let V'₀ := (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ u (circleMap z₀ r₀ θ)) (exp (↑θ * I))
    let V''₀ := (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ))
          (exp (↑θ * I))
    V''₀ + V'₀ / r₀ = 0 := by
  have hr₀_pos : 0 < r₀ := lt_of_lt_of_le hr₁ hr0
  have hC2 : ∀ θ : ℝ, ContDiffAt ℝ 2 u (circleMap z₀ r₀ θ) := by
    intro θ
    have h_in_Ω : circleMap z₀ r₀ θ ∈ Ω := by
      apply hannulus
      · rw [circleMap_sub_center]; simp [abs_of_pos hr₀_pos]; linarith
      · rw [circleMap_sub_center]; simp [abs_of_pos hr₀_pos]; linarith
    exact (hu.harmonicAt h_in_Ω).1
  have hdiff2 : ∀ θ : ℝ, DifferentiableAt ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ) := by
    intro θ; exact (hC2 θ).fderiv_right le_rfl |>.differentiableAt one_ne_zero
  have hharm : ∀ θ : ℝ, HarmonicAt u (circleMap z₀ r₀ θ) := by
    intro θ
    apply hu.harmonicAt
    apply hannulus
    · rw [circleMap_sub_center]; simp [abs_of_pos hr₀_pos]; linarith
    · rw [circleMap_sub_center]; simp [abs_of_pos hr₀_pos]; linarith
  have hV''_eq : ∀ θ : ℝ,
      (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ)) (exp (↑θ * I)) =
      (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (exp (↑θ * I)) (exp (↑θ * I)) :=
    fun θ => fderiv_eval_eq_fderiv2 (hdiff2 θ)
  have hharm_neg : ∀ θ : ℝ,
      (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (exp (↑θ * I)) (exp (↑θ * I)) =
      -((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * exp (↑θ * I)) (I * exp (↑θ * I))) := by
    intro θ
    exact harmonic_second_deriv_neg (hharm θ) (cexp_re_sq_add_im_sq θ)
  have hV''_neg : ∀ θ : ℝ,
      (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ)) (exp (↑θ * I)) =
      -((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * exp (↑θ * I)) (I * exp (↑θ * I))) :=
    fun θ => (hV''_eq θ).trans (hharm_neg θ)
  simp only [hV''_neg]
  have hperiod := periodicity_of_circle_derivative hC2
  have hint_neg : (∫ θ in (0:ℝ)..2 * π,
      -((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * cexp (↑θ * I)))
        (I * cexp (↑θ * I))) =
      -(∫ θ in (0:ℝ)..2 * π,
        ((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * cexp (↑θ * I)))
          (I * cexp (↑θ * I))) := intervalIntegral.integral_neg
  rw [hint_neg]
  simp only [smul_eq_mul]
  rw [← hperiod]
  have hr_ne : r₀ ≠ 0 := ne_of_gt hr₀_pos
  field_simp
  ring

theorem harmonic_circleAverage_euler_ode
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    ∃ V' V'' : ℝ → ℝ,
      (∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt (fun s => circleAverage u z₀ s) (V' r) r) ∧
      (∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt V' (V'' r) r) ∧
      (∀ r, r₁ ≤ r → r ≤ r₂ → V'' r + V' r / r = 0) := by
  refine ⟨fun r => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
      (fderiv ℝ u (circleMap z₀ r θ)) (exp (↑θ * I)),
    fun r => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
      (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r θ))
        (exp (↑θ * I)),
    ?_, ?_, ?_⟩
  · intro r hr hr2
    exact circleAverage_hasDerivAt_first hu hΩ hr₁ hr₁₂ hr hr2 hannulus
  · intro r hr hr2
    exact circleAverage_hasDerivAt_second hu hΩ hr₁ hr₁₂ hr hr2 hannulus
  · intro r hr hr2
    exact euler_ode_from_laplacian hu hΩ hr₁ hr₁₂ hr hr2 hannulus

theorem euler_ode_solution
    (V : ℝ → ℝ) (V' V'' : ℝ → ℝ) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁)
    (hV : ∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt V (V' r) r)
    (hV' : ∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt V' (V'' r) r)
    (hode : ∀ r, r₁ ≤ r → r ≤ r₂ → V'' r + V' r / r = 0) :
    ∃ α : ℝ, ∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt V (α / r) r := by
  set W := fun r => r * V' r
  have hW_deriv : ∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt W 0 r := by
    intro r hr1 hr2
    have hd1 : HasDerivAt (fun s => s) 1 r := hasDerivAt_id r
    have hd2 : HasDerivAt V' (V'' r) r := hV' r hr1 hr2
    have hd3 : HasDerivAt W (1 * V' r + r * V'' r) r := hd1.mul hd2
    have hr_ne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₁ hr1)
    have hV''_val : V'' r = -(V' r / r) := by linarith [hode r hr1 hr2]
    have key : V' r + r * V'' r = 0 := by
      rw [hV''_val, mul_neg, mul_div_cancel₀ _ hr_ne]; linarith
    simp only [one_mul] at hd3
    rwa [show (0 : ℝ) = V' r + r * V'' r from key.symm]
  have hW_cont : ContinuousOn W (Icc r₁ r₂) :=
    fun x hx => (hW_deriv x hx.1 hx.2).continuousAt.continuousWithinAt
  have hW_const : ∀ r, r₁ ≤ r → r ≤ r₂ → W r = W r₁ := by
    intro r hr1 hr2
    exact eq_of_has_deriv_right_eq
      (fun x hx => (hW_deriv x hx.1 (le_of_lt hx.2)).hasDerivWithinAt)
      (fun x _ => hasDerivWithinAt_const x _ _)
      hW_cont continuousOn_const rfl r ⟨hr1, hr2⟩
  use W r₁
  intro r hr1 hr2
  have hW_eq : W r = W r₁ := hW_const r hr1 hr2
  have hr_ne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₁ hr1)
  have hVr : V' r = W r₁ / r := by
    have : r * V' r = W r₁ := hW_eq
    field_simp at this ⊢; linarith
  rw [show W r₁ / r = V' r from hVr.symm]
  exact hV r hr1 hr2

theorem harmonic_circleAverage_ode
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    ∃ α : ℝ, ∀ r, r₁ ≤ r → r ≤ r₂ →
      HasDerivAt (fun s => circleAverage u z₀ s) (α / r) r := by
  obtain ⟨V', V'', hV, hV', hode⟩ := harmonic_circleAverage_euler_ode hu hΩ hr₁ hr₁₂ hannulus
  exact euler_ode_solution _ V' V'' r₁ r₂ hr₁ hV hV' hode

theorem harmonic_annulus_mean_value
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    ∃ α β : ℝ, ∀ r, r₁ ≤ r → r ≤ r₂ →
      circleAverage u z₀ r = α * Real.log r + β := by
  obtain ⟨α, hode⟩ := harmonic_circleAverage_ode hu hΩ hr₁ hr₁₂ hannulus
  set V := fun s => circleAverage u z₀ s
  set g := fun s => α * Real.log s
  refine ⟨α, V r₁ - g r₁, ?_⟩
  intro r hr1 hr2
  suffices h : V r = g r + (V r₁ - g r₁) by linarith
  have hV_cont : ContinuousOn V (Icc r₁ r₂) :=
    fun x hx => (hode x hx.1 hx.2).continuousAt.continuousWithinAt
  have hg_cont : ContinuousOn g (Icc r₁ r₂) :=
    (continuousOn_const.mul (continuousOn_id.log fun x hx => ne_of_gt (lt_of_lt_of_le hr₁ hx.1)))
  have hgc_cont : ContinuousOn (fun s => g s + (V r₁ - g r₁)) (Icc r₁ r₂) :=
    hg_cont.add continuousOn_const
  have hV_deriv : ∀ x ∈ Ico r₁ r₂, HasDerivWithinAt V (α / x) (Ici x) x :=
    fun x hx => (hode x hx.1 (le_of_lt hx.2)).hasDerivWithinAt
  have hgc_deriv : ∀ x ∈ Ico r₁ r₂,
      HasDerivWithinAt (fun s => g s + (V r₁ - g r₁)) (α / x) (Ici x) x := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₁ hx.1)
    have hg_at : HasDerivAt g (α * x⁻¹) x := (hasDerivAt_log hxne).const_mul α
    have hconst_at : HasDerivAt (fun _ => V r₁ - g r₁) 0 x := hasDerivAt_const x _
    have h := hg_at.add hconst_at
    simp only [add_zero] at h
    rw [show α / x = α * x⁻¹ from div_eq_mul_inv α x]
    exact h.hasDerivWithinAt
  exact eq_of_has_deriv_right_eq hV_deriv hgc_deriv hV_cont hgc_cont (by ring) r ⟨hr1, hr2⟩

/-- **Circle averages on an annulus** (Theorem 20). If `u` is harmonic on the closed annulus
`r₁ ≤ ‖z - z₀‖ ≤ r₂` with `0 < r₁`, then `circleAverage u z₀ r = α log r + β` for
`r ∈ [r₁, r₂]`. -/
public theorem HarmonicOnNhd.exists_circleAverage_eq_mul_log_add {u : ℂ → ℝ} {z₀ : ℂ}
    {r₁ r₂ : ℝ} (hu : HarmonicOnNhd u {z | r₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r₂}) (hr₁ : 0 < r₁) :
    ∃ α β : ℝ, ∀ r ∈ Icc r₁ r₂, circleAverage u z₀ r = α * Real.log r + β := by
  rcases le_or_gt r₁ r₂ with h₁₂ | h₂₁
  · obtain ⟨α, β, h⟩ := harmonic_annulus_mean_value (Ω := {x | HarmonicAt u x})
      (fun _ hx => hx) (isOpen_setOfPred_harmonicAt u) hr₁ h₁₂ fun z h₁ h₂ => hu z ⟨h₁, h₂⟩
    exact ⟨α, β, fun r hr => h r hr.1 hr.2⟩
  · exact ⟨0, 0, fun r hr => absurd (hr.1.trans hr.2) (not_le.2 h₂₁)⟩

end InnerProductSpace

