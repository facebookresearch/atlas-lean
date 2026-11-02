/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoDensity
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Algebraic properties of the Itô integral

The `L²` extension defining `ProbabilityTheory.itoIntegralL2` preserves the distance between any
two Itô-approximable integrands. Since it sends the zero integrand to zero, Hilbert-space geometry
then forces it to preserve real scalar multiplication and midpoints, hence addition. The selected
representatives `ProbabilityTheory.itoIntegral` inherit these identities almost surely. Combining
linearity with the existing one-integrand Itô isometry gives the two-integrand difference isometry.

## Main results

* `ProbabilityTheory.integrandDist_eq_dist_sq_itoIntegralL2`: the two-integrand
  `L²` distance isometry for Itô-approximable processes.
* `ProbabilityTheory.itoIntegral_add_of_isPreBrownianReal`: additivity for progressive
  square-integrable integrands against a pre-Brownian motion.
* `ProbabilityTheory.itoIntegral_smul_of_isPreBrownianReal`: real homogeneity in the same
  generality.
* `ProbabilityTheory.itoIntegral_isometry_sub_of_isPreBrownianReal`: the finite `L²` difference
  identity in the same generality.
* `ProbabilityTheory.itoIntegral_add`, `ProbabilityTheory.itoIntegral_smul`, and
  `ProbabilityTheory.itoIntegral_isometry_sub`: the original Brownian-motion interfaces.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal ENNReal InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

private theorem tendsto_integrandDist_pair {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    [IsFiniteMeasure P] {H K : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}
    (hH : Measurable fun p : ℝ × Ω ↦ restrictIoc H t p.1.toNNReal p.2)
    (hK : Measurable fun p : ℝ × Ω ↦ restrictIoc K t p.1.toNNReal p.2)
    {An Kn : ℕ → ElementaryIntegrand F}
    (hA : Tendsto (fun n ↦ integrandDist P (An n).toProcess H t) atTop (𝓝 0))
    (hKn : Tendsto (fun n ↦ integrandDist P (Kn n).toProcess K t) atTop (𝓝 0)) :
    Tendsto (fun n ↦ integrandDist P (An n).toProcess (Kn n).toProcess t) atTop
      (𝓝 (integrandDist P H K t)) := by
  set μ' := P.prod (volume.restrict (Set.Ioc (0 : ℝ) t))
  set eA : ℕ → ℝ≥0∞ := fun n ↦ eLpNorm (fun p : Ω × ℝ ↦
    (An n).toProcess p.2.toNNReal p.1 - H p.2.toNNReal p.1) 2 μ'
  set eK : ℕ → ℝ≥0∞ := fun n ↦ eLpNorm (fun p : Ω × ℝ ↦
    (Kn n).toProcess p.2.toNNReal p.1 - K p.2.toNNReal p.1) 2 μ'
  have tendsto_of_pow_two {e : ℕ → ℝ≥0∞}
      (he : Tendsto (fun n ↦ e n ^ 2) atTop (𝓝 0)) : Tendsto e atTop (𝓝 0) := by
    have key : ∀ x : ℝ≥0∞, (x ^ 2) ^ ((2 : ℝ)⁻¹) = x := fun x ↦ by
      simpa using ENNReal.pow_rpow_inv_natCast (n := 2) two_ne_zero x
    have h := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0 |>.comp he
    simpa [Function.comp_def, key, ENNReal.zero_rpow_of_pos] using h
  have hAe : Tendsto eA atTop (𝓝 0) := tendsto_of_pow_two (by
    refine hA.congr fun n ↦ ?_
    exact integrandDist_eq_eLpNorm_sq
      (measurable_restrictIoc (An n).measurable_toProcess t) hH)
  have hKe : Tendsto eK atTop (𝓝 0) := tendsto_of_pow_two (by
    refine hKn.congr fun n ↦ ?_
    exact integrandDist_eq_eLpNorm_sq
      (measurable_restrictIoc (Kn n).measurable_toProcess t) hK)
  set e : ℕ → ℝ≥0∞ := fun n ↦ eLpNorm (fun p : Ω × ℝ ↦
    ((An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1) -
      (H p.2.toNNReal p.1 - K p.2.toNNReal p.1)) 2 μ'
  have he_le : ∀ n, e n ≤ eA n + eK n := fun n ↦ by
    have h := eLpNorm_sub_le (μ := μ') (p := 2)
      (f := fun p : Ω × ℝ ↦ (An n).toProcess p.2.toNNReal p.1 - H p.2.toNNReal p.1)
      (g := fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1 - K p.2.toNNReal p.1)
      one_le_two
    have hfun :
        ((fun p : Ω × ℝ ↦ (An n).toProcess p.2.toNNReal p.1 - H p.2.toNNReal p.1) -
          fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1 - K p.2.toNNReal p.1) =
        fun p : Ω × ℝ ↦
          ((An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1) -
            (H p.2.toNNReal p.1 - K p.2.toNNReal p.1) := by
      funext p
      simp only [Pi.sub_apply]
      ring
    rw [hfun] at h
    simpa only [e, eA, eK] using h
  have hAeK : Tendsto (fun n ↦ eA n + eK n) atTop (𝓝 0) := by
    simpa using hAe.add hKe
  have he : Tendsto e atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAeK
      (fun _ ↦ bot_le) he_le
  set Nn : ℕ → ℝ≥0∞ := fun n ↦ eLpNorm (fun p : Ω × ℝ ↦
    (An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1) 2 μ'
  set N : ℝ≥0∞ := eLpNorm
    (fun p : Ω × ℝ ↦ H p.2.toNNReal p.1 - K p.2.toNNReal p.1) 2 μ'
  have hle1 : ∀ n, N ≤ Nn n + e n := fun n ↦ by
    have h := eLpNorm_sub_le (μ := μ') (p := 2)
      (f := fun p : Ω × ℝ ↦
        (An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1)
      (g := fun p : Ω × ℝ ↦
        ((An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1) -
          (H p.2.toNNReal p.1 - K p.2.toNNReal p.1)) one_le_two
    have hfun :
        ((fun p : Ω × ℝ ↦
          (An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1) -
          fun p : Ω × ℝ ↦
            ((An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1) -
              (H p.2.toNNReal p.1 - K p.2.toNNReal p.1)) =
        fun p : Ω × ℝ ↦ H p.2.toNNReal p.1 - K p.2.toNNReal p.1 := by
      funext p
      simp only [Pi.sub_apply]
      ring
    rw [hfun] at h
    simpa only [N, Nn, e] using h
  have hle2 : ∀ n, Nn n ≤ N + e n := fun n ↦ by
    have h := eLpNorm_add_le (μ := μ') (p := 2)
      (f := fun p : Ω × ℝ ↦ H p.2.toNNReal p.1 - K p.2.toNNReal p.1)
      (g := fun p : Ω × ℝ ↦
        ((An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1) -
          (H p.2.toNNReal p.1 - K p.2.toNNReal p.1)) one_le_two
    have hfun :
        ((fun p : Ω × ℝ ↦ H p.2.toNNReal p.1 - K p.2.toNNReal p.1) +
          fun p : Ω × ℝ ↦
            ((An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1) -
              (H p.2.toNNReal p.1 - K p.2.toNNReal p.1)) =
        fun p : Ω × ℝ ↦
          (An n).toProcess p.2.toNNReal p.1 - (Kn n).toProcess p.2.toNNReal p.1 := by
      funext p
      simp only [Pi.add_apply]
      ring
    rw [hfun] at h
    simpa only [N, Nn, e] using h
  have hNn : ∀ n, Nn n ≠ ∞ := by
    intro n hn
    apply (An n).integrandDist_ne_top (P := P) (Kn n) t
    have hsquare : integrandDist P (An n).toProcess (Kn n).toProcess t = Nn n ^ 2 := by
      simpa only [Nn] using integrandDist_eq_eLpNorm_sq
        (measurable_restrictIoc (An n).measurable_toProcess t)
        (measurable_restrictIoc (Kn n).measurable_toProcess t)
    rw [hsquare, hn, ENNReal.top_pow two_ne_zero]
  have hN : N ≠ ∞ := by
    obtain ⟨n, hn⟩ := (he.eventually (gt_mem_nhds zero_lt_one)).exists
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hNn n, (hn.trans ENNReal.one_lt_top).ne⟩) (hle1 n)
  have hconv : Tendsto Nn atTop (𝓝 N) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n ↦ N - e n)
      (h := fun n ↦ N + e n) ?_ ?_ (fun n ↦ tsub_le_iff_right.mpr (hle1 n)) hle2
    · simpa using ENNReal.Tendsto.sub tendsto_const_nhds he (Or.inl hN)
    · simpa using (tendsto_const_nhds (x := N)).add he
  have hconv2 := ENNReal.Tendsto.pow (n := 2) hconv
  have htarget : integrandDist P H K t = N ^ 2 :=
    integrandDist_eq_eLpNorm_sq hH hK
  rw [htarget]
  refine hconv2.congr fun n ↦ ?_
  exact (integrandDist_eq_eLpNorm_sq
    (measurable_restrictIoc (An n).measurable_toProcess t)
    (measurable_restrictIoc (Kn n).measurable_toProcess t)).symm

/-- The squared `L²(P ⊗ du)` distance between two Itô-approximable integrands is the squared
`L²(P)` distance between their Itô integrals. -/
theorem integrandDist_eq_dist_sq_itoIntegralL2 {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H K : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (hH : IsItoApproximable P F H t)
    (hK : IsItoApproximable P F K t) :
    integrandDist P H K t = ENNReal.ofReal
      (dist (itoIntegralL2 P F B H t) (itoIntegralL2 P F B K t) ^ 2) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨hHm, An, hA⟩ := hH
  obtain ⟨hKm, Kn, hKn⟩ := hK
  have hleft := tendsto_integrandDist_pair hHm hKm hA hKn
  have hAH := tendsto_toL2_itoIntegral hB hBF hInd hHm hA
  have hKK := tendsto_toL2_itoIntegral hB hBF hInd hKm hKn
  have hright := (ENNReal.continuous_ofReal.tendsto _).comp ((hAH.dist hKK).pow 2)
  have hright' : Tendsto
      (fun n ↦ integrandDist P (An n).toProcess (Kn n).toProcess t) atTop
      (𝓝 (ENNReal.ofReal
        (dist (itoIntegralL2 P F B H t) (itoIntegralL2 P F B K t) ^ 2))) :=
    hright.congr fun n ↦
      (ElementaryIntegrand.integrandDist_eq_dist_sq (An n) (Kn n) hB hBF hInd t).symm
  exact tendsto_nhds_unique hleft hright'

private theorem integrandDist_eq_const_mul {P : Measure Ω}
    {A B H K : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (c : ℝ)
    (h : ∀ u ω, A u ω - B u ω = c * (H u ω - K u ω)) :
    integrandDist P A B t = ‖c‖ₑ ^ 2 * integrandDist P H K t := by
  have hc : ‖c‖ₑ ^ 2 ≠ ∞ := by simp
  unfold integrandDist
  calc
    (∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖A u.toNNReal ω - B u.toNNReal ω‖ₑ ^ 2) ∂P) =
        ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
          ‖c‖ₑ ^ 2 * ‖H u.toNNReal ω - K u.toNNReal ω‖ₑ ^ 2) ∂P := by
      refine lintegral_congr fun ω ↦ setLIntegral_congr_fun measurableSet_Ioc fun u _ ↦ ?_
      rw [h, enorm_mul, mul_pow]
    _ = ∫⁻ ω, ‖c‖ₑ ^ 2 *
        (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω - K u.toNNReal ω‖ₑ ^ 2) ∂P := by
      refine lintegral_congr fun ω ↦ ?_
      exact lintegral_const_mul' _ _ hc
    _ = ‖c‖ₑ ^ 2 *
        ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
          ‖H u.toNNReal ω - K u.toNNReal ω‖ₑ ^ 2) ∂P :=
      lintegral_const_mul' _ _ hc

private theorem integrandDist_toReal_const_mul {P : Measure Ω}
    {A B H K : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (c : ℝ)
    (h : ∀ u ω, A u ω - B u ω = c * (H u ω - K u ω)) :
    (integrandDist P A B t).toReal = c ^ 2 * (integrandDist P H K t).toReal := by
  rw [integrandDist_eq_const_mul c h, ENNReal.toReal_mul, ENNReal.toReal_pow,
    Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg c), sq_abs]

private theorem itoIntegralL2_zero {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (t : ℝ≥0) : itoIntegralL2 P F B (fun _ _ ↦ (0 : ℝ)) t = 0 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h0 : IsItoApproximable P F (fun _ _ ↦ (0 : ℝ)) t :=
    isItoApproximable_of_isProgressive (isProgressive_const F 0) t (by simp)
  have hsq : ∫⁻ ω, ‖itoIntegral P F B (fun _ _ ↦ (0 : ℝ)) t ω‖ₑ ^ 2 ∂P = 0 := by
    simpa using lintegral_itoIntegral_sq hB hBF hInd h0
  have hmem := memLp_itoIntegral P F B (fun _ _ ↦ (0 : ℝ)) t
  have henorm : (fun ω ↦ ‖itoIntegral P F B (fun _ _ ↦ (0 : ℝ)) t ω‖ₑ ^ 2) =ᵐ[P]
      0 := (lintegral_eq_zero_iff'
        (hmem.aestronglyMeasurable.enorm.pow_const 2)).mp hsq
  have hzero : itoIntegral P F B (fun _ _ ↦ (0 : ℝ)) t =ᵐ[P] 0 := by
    filter_upwards [henorm] with ω hω
    simpa using hω
  refine Lp.ext ?_
  filter_upwards [(itoIntegral_ae_eq P F B (fun _ _ ↦ (0 : ℝ)) t).symm,
    hzero] with ω h1 h2
  simp [h1, h2]

private theorem itoIntegralL2_smul {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (a : ℝ) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegralL2 P F B (a • H) t = a • itoIntegralL2 P F B H t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hHa : IsProgressive F (a • H) := by
    have heq : a • H = fun u ω ↦ a * H u ω := by
      funext u ω
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact (isProgressive_const F a).mul hH
  have hD : integrandDist P H (fun _ _ ↦ (0 : ℝ)) t ≠ ∞ := by
    simpa [integrandDist] using hH2
  have hscale0 : integrandDist P (a • H) (fun _ _ ↦ (0 : ℝ)) t =
      ‖a‖ₑ ^ 2 * integrandDist P H (fun _ _ ↦ (0 : ℝ)) t :=
    integrandDist_eq_const_mul a (fun u ω ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
  have hHa2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖(a • H) u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
    have : integrandDist P (a • H) (fun _ _ ↦ (0 : ℝ)) t ≠ ∞ := by
      rw [hscale0]
      exact ENNReal.mul_ne_top (by simp) hD
    simpa [integrandDist] using this
  have hHapp := isItoApproximable_of_isProgressive hH t hH2
  have hHaapp := isItoApproximable_of_isProgressive hHa t hHa2
  have h0app : IsItoApproximable P F (fun _ _ ↦ (0 : ℝ)) t :=
    isItoApproximable_of_isProgressive (isProgressive_const F 0) t (by simp)
  have hzero := itoIntegralL2_zero hB hBF hInd t
  set x := itoIntegralL2 P F B H t
  set z := itoIntegralL2 P F B (a • H) t
  set E := (integrandDist P H (fun _ _ ↦ (0 : ℝ)) t).toReal
  have hx : ‖x‖ ^ 2 = E := by
    have h := congrArg ENNReal.toReal
      (integrandDist_eq_dist_sq_itoIntegralL2 hB hBF hInd hHapp h0app)
    simpa [x, E, hzero, ENNReal.toReal_ofReal (sq_nonneg _)] using h.symm
  have hscale0R :
      (integrandDist P (a • H) (fun _ _ ↦ (0 : ℝ)) t).toReal = a ^ 2 * E := by
    simpa [E] using congrArg ENNReal.toReal hscale0
  have hz : ‖z‖ ^ 2 = a ^ 2 * E := by
    have h := congrArg ENNReal.toReal
      (integrandDist_eq_dist_sq_itoIntegralL2 hB hBF hInd hHaapp h0app)
    simpa [z, hzero, ENNReal.toReal_ofReal (sq_nonneg _)] using h.symm.trans hscale0R
  have hscale1 : (integrandDist P (a • H) H t).toReal =
      (a - 1) ^ 2 * E := by
    simpa [E] using integrandDist_toReal_const_mul (P := P) (t := t) (a - 1)
      (A := a • H) (B := H) (H := H) (K := fun _ _ ↦ (0 : ℝ)) (fun u ω ↦ by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring)
  have hzx : ‖z - x‖ ^ 2 = (a - 1) ^ 2 * E := by
    have h := congrArg ENNReal.toReal
      (integrandDist_eq_dist_sq_itoIntegralL2 hB hBF hInd hHaapp hHapp)
    simpa [z, x, dist_eq_norm, ENNReal.toReal_ofReal (sq_nonneg _)] using
      h.symm.trans hscale1
  have hinner : ⟪z, x⟫_ℝ = a * E := by
    nlinarith [norm_sub_sq_real z x]
  have hnorm : ‖z - a • x‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    nlinarith [sq_abs a]
  have hnorm0 : ‖z - a • x‖ = 0 := by nlinarith [norm_nonneg (z - a • x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

private theorem add_energy_ne_top {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂)
    (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖(H₁ + H₂) u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
  have h1 : integrandDist P H₁ (fun _ _ ↦ (0 : ℝ)) t ≠ ∞ := by
    simpa [integrandDist] using hH₁2
  have h2 : integrandDist P H₂ (fun _ _ ↦ (0 : ℝ)) t ≠ ∞ := by
    simpa [integrandDist] using hH₂2
  have hsum : integrandDist P (H₁ + H₂) (fun _ _ ↦ (0 : ℝ)) t ≠ ∞ := by
    have h1m := IsProgressive.measurable_toNNReal hH₁
    have h2m := IsProgressive.measurable_toNNReal hH₂
    have hle := integrandDist_le (P := P) (X := H₁ + H₂)
      (Y := fun _ _ ↦ (0 : ℝ)) (Z := H₁) (h1m.add h2m) measurable_const h1m t
    have ha : integrandDist P (H₁ + H₂) H₁ t =
        integrandDist P H₂ (fun _ _ ↦ (0 : ℝ)) t := by
      simpa using integrandDist_eq_const_mul (P := P) (A := H₁ + H₂) (B := H₁)
        (H := H₂) (K := fun _ _ ↦ (0 : ℝ)) (t := t) 1 (fun u ω ↦ by
        simp only [Pi.add_apply]
        ring)
    have hb : integrandDist P (fun _ _ ↦ (0 : ℝ)) H₁ t =
        integrandDist P H₁ (fun _ _ ↦ (0 : ℝ)) t := by
      simpa using integrandDist_eq_const_mul (P := P) (A := fun _ _ ↦ (0 : ℝ))
        (B := H₁) (H := H₁) (K := fun _ _ ↦ (0 : ℝ)) (t := t) (-1)
          (fun u ω ↦ by ring)
    rw [ha, hb] at hle
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num) h2, ENNReal.mul_ne_top (by norm_num) h1⟩) hle
  simpa [integrandDist] using hsum

private theorem itoIntegralL2_add {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂)
    (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegralL2 P F B (H₁ + H₂) t =
      itoIntegralL2 P F B H₁ t + itoIntegralL2 P F B H₂ t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hsumP : IsProgressive F (H₁ + H₂) := hH₁.add hH₂
  have hsum2 := add_energy_ne_top hH₁ hH₂ t hH₁2 hH₂2
  have hmP : IsProgressive F ((1 / 2 : ℝ) • (H₁ + H₂)) := by
    have heq : (1 / 2 : ℝ) • (H₁ + H₂) =
        fun u ω ↦ (1 / 2 : ℝ) * (H₁ + H₂) u ω := by
      funext u ω
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact (isProgressive_const F (1 / 2 : ℝ)).mul hsumP
  have hsumD : integrandDist P (H₁ + H₂) (fun _ _ ↦ (0 : ℝ)) t ≠ ∞ := by
    simpa [integrandDist] using hsum2
  have hmScale : integrandDist P ((1 / 2 : ℝ) • (H₁ + H₂))
      (fun _ _ ↦ (0 : ℝ)) t = ‖(1 / 2 : ℝ)‖ₑ ^ 2 *
        integrandDist P (H₁ + H₂) (fun _ _ ↦ (0 : ℝ)) t :=
    integrandDist_eq_const_mul (1 / 2 : ℝ) (fun u ω ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
  have hm2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖((1 / 2 : ℝ) • (H₁ + H₂)) u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
    have : integrandDist P ((1 / 2 : ℝ) • (H₁ + H₂))
        (fun _ _ ↦ (0 : ℝ)) t ≠ ∞ := by
      rw [hmScale]
      exact ENNReal.mul_ne_top (by simp) hsumD
    simpa [integrandDist] using this
  have h1app := isItoApproximable_of_isProgressive hH₁ t hH₁2
  have h2app := isItoApproximable_of_isProgressive hH₂ t hH₂2
  have hmapp := isItoApproximable_of_isProgressive hmP t hm2
  set x := itoIntegralL2 P F B H₁ t
  set y := itoIntegralL2 P F B H₂ t
  set z := itoIntegralL2 P F B ((1 / 2 : ℝ) • (H₁ + H₂)) t
  set d := (integrandDist P H₁ H₂ t).toReal
  have hm1 : (integrandDist P ((1 / 2 : ℝ) • (H₁ + H₂)) H₁ t).toReal =
      (-1 / 2 : ℝ) ^ 2 * d :=
    integrandDist_toReal_const_mul (P := P) (t := t) (-1 / 2 : ℝ)
      (A := (1 / 2 : ℝ) • (H₁ + H₂)) (B := H₁) (H := H₁) (K := H₂)
      (fun u ω ↦ by
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        ring)
  have hm2' : (integrandDist P ((1 / 2 : ℝ) • (H₁ + H₂)) H₂ t).toReal =
      (1 / 2 : ℝ) ^ 2 * d :=
    integrandDist_toReal_const_mul (P := P) (t := t) (1 / 2 : ℝ)
      (A := (1 / 2 : ℝ) • (H₁ + H₂)) (B := H₂) (H := H₁) (K := H₂)
      (fun u ω ↦ by
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        ring)
  have hzx : dist z x ^ 2 = (-1 / 2 : ℝ) ^ 2 * d := by
    have h := congrArg ENNReal.toReal
      (integrandDist_eq_dist_sq_itoIntegralL2 hB hBF hInd hmapp h1app)
    simpa [z, x, ENNReal.toReal_ofReal (sq_nonneg _)] using h.symm.trans hm1
  have hzy : dist z y ^ 2 = (1 / 2 : ℝ) ^ 2 * d := by
    have h := congrArg ENNReal.toReal
      (integrandDist_eq_dist_sq_itoIntegralL2 hB hBF hInd hmapp h2app)
    simpa [z, y, ENNReal.toReal_ofReal (sq_nonneg _)] using h.symm.trans hm2'
  have hxy : dist x y ^ 2 = d := by
    have h := congrArg ENNReal.toReal
      (integrandDist_eq_dist_sq_itoIntegralL2 hB hBF hInd h1app h2app)
    simpa [x, y, d, ENNReal.toReal_ofReal (sq_nonneg _)] using h.symm
  have hxhalf : dist x z = dist x y / 2 := by
    apply (sq_eq_sq₀ (dist_nonneg) (by positivity)).mp
    calc
      dist x z ^ 2 = dist z x ^ 2 := by rw [dist_comm]
      _ = (-1 / 2 : ℝ) ^ 2 * d := hzx
      _ = (dist x y / 2) ^ 2 := by rw [← hxy]; ring
  have hyhalf : dist z y = dist x y / 2 := by
    apply (sq_eq_sq₀ (dist_nonneg) (by positivity)).mp
    calc
      dist z y ^ 2 = (1 / 2 : ℝ) ^ 2 * d := hzy
      _ = (dist x y / 2) ^ 2 := by rw [← hxy]; ring
  have hmid : z = midpoint ℝ x y :=
    eq_midpoint_of_dist_eq_half (x := x) (y := z) (z := y) hxhalf hyhalf
  have hsmul := itoIntegralL2_smul hB hBF hInd hsumP (1 / 2 : ℝ) t hsum2
  have hhalf : (1 / 2 : ℝ) • itoIntegralL2 P F B (H₁ + H₂) t =
      (1 / 2 : ℝ) • (x + y) := by
    rw [← hsmul]
    change z = (1 / 2 : ℝ) • (x + y)
    rw [hmid, midpoint_eq_smul_add]
    norm_num
  have hcancel := congrArg (fun q : Lp ℝ 2 P ↦ (2 : ℝ) • q) hhalf
  simpa [x, y, smul_smul] using hcancel

end

/-- **Linearity (additivity).** The Itô integral is additive in the integrand: for
`F`-progressive integrands `H₁, H₂` with `E ∫_0^t H_i² du < ∞`, the integral of the sum is almost
surely the sum of the integrals. Together with homogeneity and the difference isometry this pins
down the integral on the whole `L²` space of progressive integrands. Only the pre-Brownian
finite-dimensional laws are used; path continuity is not required. -/
public theorem itoIntegral_add_of_isPreBrownianReal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂) (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (H₁ + H₂) t =ᵐ[P]
      fun ω ↦ itoIntegral P F B H₁ t ω + itoIntegral P F B H₂ t ω := by
  have hL2 := itoIntegralL2_add hB hBF hInd hH₁ hH₂ t hH₁2 hH₂2
  have hL2ae : (itoIntegralL2 P F B (H₁ + H₂) t : Ω → ℝ) =ᵐ[P]
      fun ω ↦ (itoIntegralL2 P F B H₁ t : Ω → ℝ) ω +
        (itoIntegralL2 P F B H₂ t : Ω → ℝ) ω := by
    rw [hL2]
    exact Lp.coeFn_add _ _
  filter_upwards [itoIntegral_ae_eq P F B (H₁ + H₂) t,
    itoIntegral_ae_eq P F B H₁ t, itoIntegral_ae_eq P F B H₂ t,
    hL2ae] with ω hsum h1 h2 hL2ω
  rw [hsum, h1, h2, hL2ω]

/-- **Linearity (additivity).** The Itô integral is additive in the integrand: for
`F`-progressive integrands `H₁, H₂` with `E ∫_0^t H_i² du < ∞`, the integral of the sum is almost
surely the sum of the integrals. Together with homogeneity and the difference isometry this pins
down the integral on the whole `L²` space of progressive integrands. -/
public theorem itoIntegral_add {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂) (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (H₁ + H₂) t =ᵐ[P]
      fun ω ↦ itoIntegral P F B H₁ t ω + itoIntegral P F B H₂ t ω := by
  exact itoIntegral_add_of_isPreBrownianReal hB.toIsPreBrownianReal hBF hInd hH₁ hH₂ t
    hH₁2 hH₂2

/-- **Linearity (homogeneity).** The Itô integral is homogeneous in the integrand for a
pre-Brownian integrator; path continuity is not required. -/
public theorem itoIntegral_smul_of_isPreBrownianReal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (a : ℝ) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (a • H) t =ᵐ[P] fun ω ↦ a * itoIntegral P F B H t ω := by
  have hL2 := itoIntegralL2_smul hB hBF hInd hH a t hH2
  have hL2ae : (itoIntegralL2 P F B (a • H) t : Ω → ℝ) =ᵐ[P]
      fun ω ↦ a * (itoIntegralL2 P F B H t : Ω → ℝ) ω := by
    rw [hL2]
    filter_upwards [Lp.coeFn_smul a (itoIntegralL2 P F B H t)] with ω hω
    simpa only [Pi.smul_apply, smul_eq_mul] using hω
  filter_upwards [itoIntegral_ae_eq P F B (a • H) t,
    itoIntegral_ae_eq P F B H t, hL2ae] with ω ha h hL2ω
  rw [ha, h, hL2ω]

/-- **Linearity (homogeneity).** The Itô integral is homogeneous in the integrand. -/
public theorem itoIntegral_smul {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (a : ℝ) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (a • H) t =ᵐ[P] fun ω ↦ a * itoIntegral P F B H t ω := by
  exact itoIntegral_smul_of_isPreBrownianReal hB.toIsPreBrownianReal hBF hInd hH a t hH2

/-- **Difference isometry.** For two `F`-progressive integrands with `E ∫_0^t H_i² du < ∞`, the
difference of the integrals is square-integrable and
`E[(∫ H₁ dB - ∫ H₂ dB)²] = E ∫ (H₁ - H₂)² du`. With linearity this is the two-integrand isometry
that, together with the elementary-integrand formula, determines the construction on the whole
`L²` space. Only the pre-Brownian finite-dimensional laws are used; path continuity is not
required. -/
public theorem itoIntegral_isometry_sub_of_isPreBrownianReal {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂) (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    MemLp (fun ω ↦ itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω) 2 P ∧
      ∫⁻ ω, ‖itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω‖ₑ ^ 2 ∂P =
        ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
          ‖H₁ u.toNNReal ω - H₂ u.toNNReal ω‖ₑ ^ 2) ∂P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hD : integrandDist P H₁ H₂ t ≠ ∞ := by
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num) (by simpa [integrandDist] using hH₁2),
          ENNReal.mul_ne_top (by norm_num) (by simpa [integrandDist] using hH₂2)⟩)
      (integrandDist_le (P := P) (X := H₁) (Y := H₂)
        (Z := fun _ _ ↦ (0 : ℝ)) (IsProgressive.measurable_toNNReal hH₁)
        (IsProgressive.measurable_toNNReal hH₂) measurable_const t)
  have hsubP : IsProgressive F (H₁ - H₂) := hH₁.sub hH₂
  have hsub2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖(H₁ - H₂) u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
    simpa [integrandDist] using hD
  have hnegP : IsProgressive F ((-1 : ℝ) • H₂) := by
    have heq : (-1 : ℝ) • H₂ = fun u ω ↦ (-1 : ℝ) * H₂ u ω := by
      funext u ω
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact (isProgressive_const F (-1 : ℝ)).mul hH₂
  have hneg2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖((-1 : ℝ) • H₂) u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
    simpa using hH₂2
  have hproc : H₁ + (-1 : ℝ) • H₂ = H₁ - H₂ := by
    funext u ω
    simp [sub_eq_add_neg]
  have hadd := itoIntegral_add_of_isPreBrownianReal hB hBF hInd hH₁ hnegP t hH₁2 hneg2
  rw [hproc] at hadd
  have hneg := itoIntegral_smul_of_isPreBrownianReal hB hBF hInd hH₂ (-1) t hH₂2
  have hae : (fun ω ↦ itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω) =ᵐ[P]
      itoIntegral P F B (H₁ - H₂) t := by
    filter_upwards [hadd, hneg] with ω ha hn
    rw [ha, hn]
    ring
  refine ⟨(memLp_itoIntegral P F B H₁ t).sub (memLp_itoIntegral P F B H₂ t), ?_⟩
  calc
    (∫⁻ ω, ‖itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω‖ₑ ^ 2 ∂P) =
        ∫⁻ ω, ‖itoIntegral P F B (H₁ - H₂) t ω‖ₑ ^ 2 ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      rw [hω]
    _ = ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
        ‖(H₁ - H₂) u.toNNReal ω‖ₑ ^ 2) ∂P :=
      lintegral_itoIntegral_sq_of_isProgressive hB hBF hInd hsubP t hsub2
    _ = ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
        ‖H₁ u.toNNReal ω - H₂ u.toNNReal ω‖ₑ ^ 2) ∂P := by
      rfl

/-- **Difference isometry.** For two `F`-progressive integrands with `E ∫_0^t H_i² du < ∞`, the
difference of the integrals is square-integrable and
`E[(∫ H₁ dB - ∫ H₂ dB)²] = E ∫ (H₁ - H₂)² du`. With linearity this is the two-integrand isometry
that, together with the elementary-integrand formula, determines the construction on the whole
`L²` space. -/
public theorem itoIntegral_isometry_sub {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂) (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    MemLp (fun ω ↦ itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω) 2 P ∧
      ∫⁻ ω, ‖itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω‖ₑ ^ 2 ∂P =
        ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
          ‖H₁ u.toNNReal ω - H₂ u.toNNReal ω‖ₑ ^ 2) ∂P := by
  exact itoIntegral_isometry_sub_of_isPreBrownianReal hB.toIsPreBrownianReal hBF hInd hH₁ hH₂ t
    hH₁2 hH₂2

end ProbabilityTheory
