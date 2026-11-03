/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoIntegralProperties
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import MathlibExtTest.Probability.ItoIntegralSampleDependent

/-!
# Tests for algebraic properties of the Itô integral

The probes cover the exact Brownian wrappers, the broader pre-Brownian APIs, unequal nonzero
progressive integrands, cancellation, the scalars `0`, `1`, and `-1`, the boundary time `0`, two
distinct horizons, and off-horizon support. A sample-dependent pre-Brownian probe uses the sign
selected by `B 1` on two adjacent windows and computes its difference energy exactly. Process
hypotheses remain explicit because the base library has no concrete continuous Brownian
construction; all integrand hypotheses are discharged.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExtTest.Probability.ItoIntegralProperties

open MathlibExtTest.Probability.ItoIntegralSampleDependent

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-! The next three examples are the frozen target closure, copied binder-for-binder. -/

example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂)
    (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (H₁ + H₂) t =ᵐ[P]
      fun ω ↦ itoIntegral P F B H₁ t ω + itoIntegral P F B H₂ t ω :=
  itoIntegral_add hB hBF hInd hH₁ hH₂ t hH₁2 hH₂2

example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (a : ℝ) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (a • H) t =ᵐ[P] fun ω ↦ a * itoIntegral P F B H t ω :=
  itoIntegral_smul hB hBF hInd hH a t hH2

example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂)
    (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    MemLp (fun ω ↦ itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω) 2 P ∧
      ∫⁻ ω, ‖itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω‖ₑ ^ 2 ∂P =
        ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
          ‖H₁ u.toNNReal ω - H₂ u.toNNReal ω‖ₑ ^ 2) ∂P :=
  itoIntegral_isometry_sub hB hBF hInd hH₁ hH₂ t hH₁2 hH₂2

/-! The next three examples exercise the broader pre-Brownian APIs directly. -/

example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂)
    (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (H₁ + H₂) t =ᵐ[P]
      fun ω ↦ itoIntegral P F B H₁ t ω + itoIntegral P F B H₂ t ω :=
  itoIntegral_add_of_isPreBrownianReal hB hBF hInd hH₁ hH₂ t hH₁2 hH₂2

example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (a : ℝ) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (a • H) t =ᵐ[P] fun ω ↦ a * itoIntegral P F B H t ω :=
  itoIntegral_smul_of_isPreBrownianReal hB hBF hInd hH a t hH2

example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂)
    (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    MemLp (fun ω ↦ itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω) 2 P ∧
      ∫⁻ ω, ‖itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω‖ₑ ^ 2 ∂P =
        ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
          ‖H₁ u.toNNReal ω - H₂ u.toNNReal ω‖ₑ ^ 2) ∂P :=
  itoIntegral_isometry_sub_of_isPreBrownianReal hB hBF hInd hH₁ hH₂ t hH₁2 hH₂2

private theorem const_energy_ne_top [IsFiniteMeasure P] (c : ℝ) (t : ℝ≥0) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖(fun (_ : ℝ≥0) (_ : Ω) ↦ c) u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
  simp
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (measure_ne_top P _)

/-- Additivity for two unequal, nonzero progressive integrands needs only a pre-Brownian
integrator. -/
example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (t : ℝ≥0) :
    itoIntegral P F B
        ((fun (_ : ℝ≥0) (_ : Ω) ↦ (1 : ℝ)) + fun _ _ ↦ (2 : ℝ)) t =ᵐ[P]
      fun ω ↦ itoIntegral P F B (fun _ _ ↦ (1 : ℝ)) t ω +
        itoIntegral P F B (fun _ _ ↦ (2 : ℝ)) t ω := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact itoIntegral_add_of_isPreBrownianReal hB hBF hInd (isProgressive_const F 1)
    (isProgressive_const F 2) t (const_energy_ne_top 1 t) (const_energy_ne_top 2 t)

/-- Scalar zero sends a nonzero integrand to the zero integral. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (t : ℝ≥0) :
    itoIntegral P F B ((0 : ℝ) •
      (fun (_ : ℝ≥0) (_ : Ω) ↦ (2 : ℝ))) t =ᵐ[P]
        fun ω ↦ (0 : ℝ) * itoIntegral P F B (fun _ _ ↦ (2 : ℝ)) t ω := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact itoIntegral_smul hB hBF hInd (isProgressive_const F 2) 0 t
    (const_energy_ne_top 2 t)

/-- Scalar one preserves the selected representative almost surely. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (t : ℝ≥0) :
    itoIntegral P F B ((1 : ℝ) •
      (fun (_ : ℝ≥0) (_ : Ω) ↦ (2 : ℝ))) t =ᵐ[P]
      fun ω ↦ (1 : ℝ) * itoIntegral P F B (fun _ _ ↦ (2 : ℝ)) t ω := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact itoIntegral_smul hB hBF hInd (isProgressive_const F 2) 1 t
    (const_energy_ne_top 2 t)

/-- Scalar `-1` negates the integral under the pre-Brownian hypotheses. -/
example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (t : ℝ≥0) :
    itoIntegral P F B ((-1 : ℝ) •
      (fun (_ : ℝ≥0) (_ : Ω) ↦ (2 : ℝ))) t =ᵐ[P]
      fun ω ↦ -itoIntegral P F B (fun _ _ ↦ (2 : ℝ)) t ω := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  simpa using itoIntegral_smul_of_isPreBrownianReal hB hBF hInd
    (isProgressive_const F 2) (-1) t (const_energy_ne_top 2 t)

/-- Addition and scalar `-1` give cancellation for a nonzero integrand. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (t : ℝ≥0) :
    itoIntegral P F B ((fun (_ : ℝ≥0) (_ : Ω) ↦ (2 : ℝ)) +
      (-1 : ℝ) • (fun (_ : ℝ≥0) (_ : Ω) ↦ (2 : ℝ))) t =ᵐ[P] 0 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hneg : IsProgressive F
      ((-1 : ℝ) • (fun (_ : ℝ≥0) (_ : Ω) ↦ (2 : ℝ))) := by
    have heq : ((-1 : ℝ) • (fun (_ : ℝ≥0) (_ : Ω) ↦ (2 : ℝ))) =
        fun (_ : ℝ≥0) (_ : Ω) ↦ (-2 : ℝ) := by
      funext u ω
      simp only [Pi.smul_apply, smul_eq_mul]
      norm_num
    rw [heq]
    exact isProgressive_const F (-2 : ℝ)
  have hneg2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖(((-1 : ℝ) • (fun (_ : ℝ≥0) (_ : Ω) ↦ (2 : ℝ))) u.toNNReal ω)‖ₑ ^ 2)
        ∂P ≠ ∞ := by
    simpa using const_energy_ne_top (P := P) (-2) t
  filter_upwards [itoIntegral_add hB hBF hInd (isProgressive_const F 2) hneg t
      (const_energy_ne_top 2 t) hneg2,
    itoIntegral_smul hB hBF hInd (isProgressive_const F 2) (-1) t
      (const_energy_ne_top 2 t)] with ω hadd hsmul
  rw [hadd, hsmul]
  simp

/-- At time `0`, the difference isometry has zero energy for arbitrary progressive inputs. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂) :
    MemLp (fun ω ↦ itoIntegral P F B H₁ 0 ω - itoIntegral P F B H₂ 0 ω) 2 P ∧
      ∫⁻ ω, ‖itoIntegral P F B H₁ 0 ω - itoIntegral P F B H₂ 0 ω‖ₑ ^ 2 ∂P = 0 := by
  simpa using itoIntegral_isometry_sub hB hBF hInd hH₁ hH₂ 0 (by simp) (by simp)

/-- Unequal constant integrands have the expected difference energy on two distinct horizons. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P) :
    (∫⁻ ω, ‖itoIntegral P F B (fun _ _ ↦ (1 : ℝ)) 1 ω -
        itoIntegral P F B (fun _ _ ↦ (2 : ℝ)) 1 ω‖ₑ ^ 2 ∂P = 1) ∧
      ∫⁻ ω, ‖itoIntegral P F B (fun _ _ ↦ (1 : ℝ)) 2 ω -
        itoIntegral P F B (fun _ _ ↦ (2 : ℝ)) 2 ω‖ₑ ^ 2 ∂P = 2 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  constructor
  · have h := (itoIntegral_isometry_sub hB hBF hInd (isProgressive_const F 1)
      (isProgressive_const F 2) 1 (const_energy_ne_top 1 1)
        (const_energy_ne_top 2 1)).2
    norm_num [Real.enorm_eq_ofReal_abs] at h
    simpa [Real.enorm_eq_ofReal_abs] using h
  · have h := (itoIntegral_isometry_sub hB hBF hInd (isProgressive_const F 1)
      (isProgressive_const F 2) 2 (const_energy_ne_top 1 2)
        (const_energy_ne_top 2 2)).2
    norm_num [Real.enorm_eq_ofReal_abs] at h
    simpa [Real.enorm_eq_ofReal_abs] using h

/-- A progressive integrand supported at time `0` and after `t`; it is zero on `(0, t]`. -/
noncomputable def outsideIoc (t : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun u _ ↦ (Set.Ioc 0 t)ᶜ.indicator (fun _ ↦ (1 : ℝ)) u

private theorem outsideIoc_progressive (t : ℝ≥0) : IsProgressive F (outsideIoc (Ω := Ω) t) := by
  intro T
  exact measurable_const.indicator
    (measurableSet_Ioc.compl.preimage (measurable_subtype_coe.comp measurable_fst))

private theorem outsideIoc_energy (t : ℝ≥0) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖outsideIoc (Ω := Ω) t u.toNNReal ω‖ₑ ^ 2) ∂P = 0 := by
  calc
    (∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖outsideIoc (Ω := Ω) t u.toNNReal ω‖ₑ ^ 2) ∂P) = ∫⁻ _ω, 0 ∂P := by
      refine lintegral_congr fun ω ↦ setLIntegral_eq_zero measurableSet_Ioc fun u hu ↦ ?_
      have hu' : u.toNNReal ∈ Set.Ioc (0 : ℝ≥0) t :=
        ⟨Real.toNNReal_pos.2 hu.1, Real.toNNReal_le_iff_le_coe.2 hu.2⟩
      simp [outsideIoc, hu']
    _ = 0 := by simp

example (t : ℝ≥0) (ω : Ω) : outsideIoc t 0 ω = 1 := by
  simp [outsideIoc]

example (t u : ℝ≥0) (htu : t < u) (ω : Ω) : outsideIoc t u ω = 1 := by
  have hu : u ∉ Set.Ioc 0 t := fun hu ↦ (not_lt_of_ge hu.2) htu
  simp [outsideIoc, hu]

/-- Values at time `0` and strictly after the horizon contribute no difference energy. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (t : ℝ≥0) :
    MemLp (fun ω ↦ itoIntegral P F B (outsideIoc t) t ω -
      itoIntegral P F B (fun _ _ ↦ (0 : ℝ)) t ω) 2 P ∧
      ∫⁻ ω, ‖itoIntegral P F B (outsideIoc t) t ω -
        itoIntegral P F B (fun _ _ ↦ (0 : ℝ)) t ω‖ₑ ^ 2 ∂P = 0 := by
  simpa [outsideIoc_energy (P := P) t] using itoIntegral_isometry_sub hB hBF hInd
    (outsideIoc_progressive t) (isProgressive_const F 0) t
    (by simp [outsideIoc_energy (P := P) t]) (by simp)

/-- A coefficient selected by `B 1` on adjacent windows has difference energy exactly `2`
under the pre-Brownian hypotheses. -/
example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P) :
    ∫⁻ ω, ‖itoIntegral P F B (signedWindow B 1 2) 3 ω -
      itoIntegral P F B (signedWindow B 2 3) 3 ω‖ₑ ^ 2 ∂P = 2 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h12 := signedWindow_progressive hBF 1 2 (by norm_num)
  have h23 := signedWindow_progressive hBF 2 3 (by norm_num)
  have h12e := signedWindow_energy_ne_top (P := P) hBF 1 2
    (by norm_num) (by norm_num) 3
  have h23e := signedWindow_energy_ne_top (P := P) hBF 2 3
    (by norm_num) (by norm_num) 3
  rw [(itoIntegral_isometry_sub_of_isPreBrownianReal hB hBF hInd h12 h23 3 h12e h23e).2]
  calc
    (∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) 3,
      ‖signedWindow B 1 2 u.toNNReal ω - signedWindow B 2 3 u.toNNReal ω‖ₑ ^ 2) ∂P) =
        ∫⁻ _ω, (∫⁻ u in Set.Ioc (0 : ℝ) 3,
          (Set.Ioc (1 : ℝ) 3).indicator (fun _ ↦ (1 : ℝ≥0∞)) u) ∂P := by
      refine lintegral_congr fun ω ↦ setLIntegral_congr_fun measurableSet_Ioc fun u _ ↦ ?_
      exact signed_windows_sq u ω
    _ = 2 := by
      norm_num [lintegral_indicator, Set.Ioc_inter_Ioc, Real.volume_Ioc]

#check @itoIntegral_add_of_isPreBrownianReal
#check @itoIntegral_smul_of_isPreBrownianReal
#check @itoIntegral_isometry_sub_of_isPreBrownianReal
#check @itoIntegral_add
#check @itoIntegral_smul
#check @itoIntegral_isometry_sub

#print axioms integrandDist_eq_dist_sq_itoIntegralL2
#print axioms itoIntegral_add_of_isPreBrownianReal
#print axioms itoIntegral_smul_of_isPreBrownianReal
#print axioms itoIntegral_isometry_sub_of_isPreBrownianReal
#print axioms itoIntegral_add
#print axioms itoIntegral_smul
#print axioms itoIntegral_isometry_sub

end MathlibExtTest.Probability.ItoIntegralProperties
