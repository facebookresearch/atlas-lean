/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `bc0a5a31aa07d127ead55e6848aa133300c4ce0a`.
Original formalization by Manasa Hariharan (@manasahari-meta); ported with permission.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Moments.Variance

/-!
# Estimation risk: bias, mean squared error, and unbiasedness

Finite bias and finite mean squared error for a fixed real estimator under a
normalized probability law. Integrability evidence is an explicit input to the
finite declarations, so nonintegrable estimators have no finite source value.
A separately labeled extended bridge preserves infinite squared error.
Unbiasedness for a target function carries integrability inside the predicate.
Under a finite second moment, MSE decomposes into variance plus squared bias.

Source: Casella-Berger Definitions 7.3.1 and 7.3.2 with equation 7.3.1 and
section 7.3.2 (blueprints `af_723199a7ca6fb3e936a73618`,
`af_fd40353442120bd19166139d`, `af_95118d196fd6478105a6eb43`,
`af_3a1bafba0b7dff99554b01f0`). The estimator map is fixed before the law and
the target value; no parameter-dependent estimator map is accepted.
-/

namespace MathlibExt.Probability.Statistics.EstimationRisk

@[expose] public section

open MeasureTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- Source finite bias of a fixed real estimator under a probability law:
expected value minus the real target. The `Integrable` input is the source
expectation domain from Chapter 2 Definition 2.2.1; without it no finite
source bias exists. Blueprint `af_723199a7ca6fb3e936a73618`. -/
noncomputable def bias (W : S → ℝ) (μ : ProbabilityMeasure S) (θ : ℝ)
    (_hW : Integrable W (μ : Measure S)) : ℝ :=
  ∫ x, W x ∂(μ : Measure S) - θ

/-- Characteristic evaluation: finite bias is the integral minus the target.
Blueprint `af_723199a7ca6fb3e936a73618`. -/
@[simp]
theorem bias_eq_integral (W : S → ℝ) (μ : ProbabilityMeasure S) (θ : ℝ)
    (hW : Integrable W (μ : Measure S)) :
    bias W μ θ hW = ∫ x, W x ∂(μ : Measure S) - θ :=
  rfl

/-- Source finite mean squared error of a fixed real estimator under a
probability law: expected squared error at the real target. The `Integrable`
input is the source expectation domain; without it no finite source MSE
exists. Blueprint `af_fd40353442120bd19166139d`. -/
noncomputable def meanSquaredError (W : S → ℝ) (μ : ProbabilityMeasure S)
    (θ : ℝ)
    (_hW2 : Integrable (fun x => (W x - θ) ^ 2) (μ : Measure S)) : ℝ :=
  ∫ x, (W x - θ) ^ 2 ∂(μ : Measure S)

/-- Characteristic evaluation: finite MSE is the squared-error integral.
Blueprint `af_fd40353442120bd19166139d`. -/
@[simp]
theorem meanSquaredError_eq_integral (W : S → ℝ) (μ : ProbabilityMeasure S)
    (θ : ℝ)
    (hW2 : Integrable (fun x => (W x - θ) ^ 2) (μ : Measure S)) :
    meanSquaredError W μ θ hW2 = ∫ x, (W x - θ) ^ 2 ∂(μ : Measure S) :=
  rfl

/-- Extended squared-error bridge: nonnegative extended integral of squared
error. This is a boundary-analysis object only. It is not the source finite
MSE; on the integrable domain it agrees with the source value by
`ofReal_meanSquaredError`, and off that domain with measurability it records
infinity by `meanSquaredErrorENN_eq_top_of_not_finite`. Blueprint
`af_fd40353442120bd19166139d`. -/
noncomputable def meanSquaredErrorENN (W : S → ℝ) (μ : ProbabilityMeasure S)
    (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((W x - θ) ^ 2) ∂(μ : Measure S)

/-- On the finite domain, the extended bridge agrees with the source finite
MSE value. Blueprint `af_fd40353442120bd19166139d`. -/
theorem ofReal_meanSquaredError {W : S → ℝ} {μ : ProbabilityMeasure S}
    {θ : ℝ}
    (h : Integrable (fun x => (W x - θ) ^ 2) (μ : Measure S)) :
    ENNReal.ofReal (meanSquaredError W μ θ h) = meanSquaredErrorENN W μ θ := by
  rw [meanSquaredError, meanSquaredErrorENN]
  exact ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall fun x => sq_nonneg (W x - θ))

/-- Off the finite domain, with measurability, the extended bridge records
infinity rather than a finite value. Blueprint
`af_fd40353442120bd19166139d`. -/
theorem meanSquaredErrorENN_eq_top_of_not_finite {W : S → ℝ}
    {μ : ProbabilityMeasure S} {θ : ℝ}
    (hm : AEStronglyMeasurable (fun x => (W x - θ) ^ 2) (μ : Measure S))
    (h : ¬ Integrable (fun x => (W x - θ) ^ 2) (μ : Measure S)) :
    meanSquaredErrorENN W μ θ = ∞ := by
  have hfin : ¬ HasFiniteIntegral (fun x => (W x - θ) ^ 2) (μ : Measure S) :=
    fun hfin => h ⟨hm, hfin⟩
  rw [HasFiniteIntegral] at hfin
  have htop : ∫⁻ x, ‖(W x - θ) ^ 2‖ₑ ∂(μ : Measure S) = ∞ :=
    le_antisymm le_top (le_of_not_gt hfin)
  rw [meanSquaredErrorENN, ← htop]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact (Real.enorm_of_nonneg (sq_nonneg (W x - θ))).symm

/-- Family bias for a single fixed estimator: at each parameter, bias under
that parameter law at the target value. The per-parameter `Integrable`
evidence is an input; `W` is fixed before the family and does not depend on
`θ`. Blueprint `af_723199a7ca6fb3e936a73618`. -/
noncomputable def familyBias {Θ : Type*} (W : S → ℝ)
    (P : Θ → ProbabilityMeasure S) (τ : Θ → ℝ)
    (h : ∀ θ, Integrable W ((P θ) : Measure S)) : Θ → ℝ :=
  fun θ => bias W (P θ) (τ θ) (h θ)

/-- Characteristic evaluation: family bias is the integral minus the target.
Blueprint `af_723199a7ca6fb3e936a73618`. -/
@[simp]
theorem familyBias_apply {Θ : Type*} (W : S → ℝ)
    (P : Θ → ProbabilityMeasure S) (τ : Θ → ℝ)
    (h : ∀ θ, Integrable W ((P θ) : Measure S)) (θ : Θ) :
    familyBias W P τ h θ = ∫ x, W x ∂((P θ) : Measure S) - τ θ :=
  rfl

/-- Family finite MSE for a single fixed estimator: at each parameter, finite
MSE under that parameter law at the target value. The per-parameter
`Integrable` evidence is an input; `W` is fixed before the family and does
not depend on `θ`. Blueprint `af_fd40353442120bd19166139d`. -/
noncomputable def familyMeanSquaredError {Θ : Type*} (W : S → ℝ)
    (P : Θ → ProbabilityMeasure S) (τ : Θ → ℝ)
    (h : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) ((P θ) : Measure S)) :
    Θ → ℝ :=
  fun θ => meanSquaredError W (P θ) (τ θ) (h θ)

/-- Characteristic evaluation: family MSE is the squared-error integral.
Blueprint `af_fd40353442120bd19166139d`. -/
@[simp]
theorem familyMeanSquaredError_apply {Θ : Type*} (W : S → ℝ)
    (P : Θ → ProbabilityMeasure S) (τ : Θ → ℝ)
    (h : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) ((P θ) : Measure S))
    (θ : Θ) :
    familyMeanSquaredError W P τ h θ =
      ∫ x, (W x - τ θ) ^ 2 ∂((P θ) : Measure S) :=
  rfl

/-- Source unbiasedness of a single fixed real estimator for a target function:
at every parameter the expectation exists and equals the target value. `W` is
fixed before the family `P` and the target `τ`; no parameter-dependent
estimator map is accepted. Integrability is inside the predicate: a
nonintegrable estimator is not unbiased even when the totalized integral
happens to match. The identity target on real parameters is the source
`§7.3.1` case; the general target is the explicit `§7.3.2` generalization.
Blueprint `af_95118d196fd6478105a6eb43`. -/
def IsUnbiased {Θ : Type*} (W : S → ℝ) (P : Θ → ProbabilityMeasure S)
    (τ : Θ → ℝ) : Prop :=
  ∀ θ, Integrable W ((P θ) : Measure S) ∧
    ∫ x, W x ∂((P θ) : Measure S) = τ θ

/-- Integrability at each parameter from unbiasedness. -/
theorem IsUnbiased.integrable {Θ : Type*} {W : S → ℝ}
    {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ} (h : IsUnbiased W P τ)
    (θ : Θ) : Integrable W ((P θ) : Measure S) :=
  (h θ).1

/-- Expectation identity at each parameter from unbiasedness. -/
theorem IsUnbiased.expect_eq {Θ : Type*} {W : S → ℝ}
    {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ} (h : IsUnbiased W P τ)
    (θ : Θ) : ∫ x, W x ∂((P θ) : Measure S) = τ θ :=
  (h θ).2

/-- Unbiasedness holds exactly when the family bias vanishes everywhere. -/
theorem isUnbiased_iff_forall_familyBias_eq_zero {Θ : Type*} {W : S → ℝ}
    {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ}
    (h : ∀ θ, Integrable W ((P θ) : Measure S)) :
    IsUnbiased W P τ ↔ ∀ θ, familyBias W P τ h θ = 0 := by
  constructor
  · intro hunb θ
    show (∫ x, W x ∂((P θ) : Measure S)) - τ θ = 0
    rw [(hunb θ).2, sub_self]
  · intro hzero θ
    refine ⟨h θ, ?_⟩
    have hz : (∫ x, W x ∂((P θ) : Measure S)) - τ θ = 0 := hzero θ
    exact sub_eq_zero.mp hz

/-- Squared-error integrability at a target derived from a finite second moment
of the estimator. -/
theorem integrable_sq_sub_of_memLp_two {W : S → ℝ} {μ : ProbabilityMeasure S}
    {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S))) :
    Integrable (fun x => (W x - θ) ^ 2) ((μ : Measure S)) := by
  have hWsub : MemLp (fun x => W x - θ) 2 ((μ : Measure S)) :=
    hW.sub (memLp_const θ)
  exact hWsub.integrable_sq

/-- Source equation 7.3.1: under a finite second moment, the finite MSE equals
the variance plus the squared bias. This bias form is the complete source
conclusion; the expectation form `(∫W - θ)²` is the same value through the
accepted `bias` definition. All integrability evidence is derived from the
`MemLp` hypothesis. Blueprint `af_3a1bafba0b7dff99554b01f0`. -/
theorem meanSquaredError_eq_variance_add_sq_bias {W : S → ℝ}
    {μ : ProbabilityMeasure S} {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S))) :
    meanSquaredError W μ θ (integrable_sq_sub_of_memLp_two hW) =
      ProbabilityTheory.variance W ((μ : Measure S)) +
        (bias W μ θ (hW.integrable one_le_two)) ^ 2 := by
  have hW1 : Integrable W ((μ : Measure S)) := hW.integrable one_le_two
  have hWsub : MemLp (fun x => W x - θ) 2 ((μ : Measure S)) :=
    hW.sub (memLp_const θ)
  have hvar := ProbabilityTheory.variance_eq_sub (μ := ((μ : Measure S))) hWsub
  rw [ProbabilityTheory.variance_sub_const hW1.aestronglyMeasurable θ] at hvar
  have hlin : ∫ x, (W x - θ) ∂((μ : Measure S))
      = (∫ x, W x ∂((μ : Measure S))) - θ := by
    have hsub := integral_sub hW1 (integrable_const θ)
    simp only [integral_const, measureReal_def,
      IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul] at hsub
    exact hsub
  rw [hlin] at hvar
  have hsq : ∫ x, (W x - θ) ^ 2 ∂((μ : Measure S))
      = ∫ x, ((fun x => W x - θ) ^ 2) x ∂((μ : Measure S)) := by
    simp [Pi.pow_apply]
  show ∫ x, (W x - θ) ^ 2 ∂((μ : Measure S)) = _ + (_ - _) ^ 2
  rw [hsq, hvar]
  ring

/-- Source equation 7.3.1 in expectation form: the finite MSE equals the
variance plus the squared deviation of the mean from the target. This is the
same value as the bias form through the accepted `bias` definition. Blueprint
`af_3a1bafba0b7dff99554b01f0`. -/
theorem meanSquaredError_eq_variance_add_sq_expectation_sub {W : S → ℝ}
    {μ : ProbabilityMeasure S} {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S))) :
    meanSquaredError W μ θ (integrable_sq_sub_of_memLp_two hW) =
      ProbabilityTheory.variance W ((μ : Measure S)) +
        ((∫ x, W x ∂((μ : Measure S))) - θ) ^ 2 :=
  meanSquaredError_eq_variance_add_sq_bias hW

/-- The extended MSE bridge records the `ofReal` of the
variance-plus-squared-bias value on the finite domain. -/
theorem ofReal_variance_add_sq_bias {W : S → ℝ} {μ : ProbabilityMeasure S}
    {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S))) :
    ENNReal.ofReal (ProbabilityTheory.variance W ((μ : Measure S)) +
          (bias W μ θ (hW.integrable one_le_two)) ^ 2) =
      meanSquaredErrorENN W μ θ := by
  rw [← meanSquaredError_eq_variance_add_sq_bias hW]
  exact ofReal_meanSquaredError _

/-- Family equation 7.3.1 for a single fixed estimator: at each parameter with
a finite second moment, family MSE equals variance plus squared family bias. -/
theorem familyMeanSquaredError_eq_variance_add_sq_familyBias {Θ : Type*}
    {W : S → ℝ} {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ}
    (hMem : ∀ θ, MemLp W 2 (((P θ)) : Measure S))
    (h2 : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) (((P θ)) : Measure S))
    (h1 : ∀ θ, Integrable W (((P θ)) : Measure S)) (θ : Θ) :
    familyMeanSquaredError W P τ h2 θ =
      ProbabilityTheory.variance W (((P θ)) : Measure S) +
        (familyBias W P τ h1 θ) ^ 2 :=
  meanSquaredError_eq_variance_add_sq_bias (hMem θ)

/-- For an unbiased estimator the finite MSE equals the variance: the bias
term vanishes. Source: the display following Definition 7.3.2. -/
theorem meanSquaredError_eq_variance_of_expect_eq {W : S → ℝ}
    {μ : ProbabilityMeasure S} {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S)))
    (hunb : ∫ x, W x ∂((μ : Measure S)) = θ) :
    meanSquaredError W μ θ (integrable_sq_sub_of_memLp_two hW) =
      ProbabilityTheory.variance W ((μ : Measure S)) := by
  have hb : bias W μ θ (hW.integrable one_le_two) = 0 := by
    show (∫ x, W x ∂((μ : Measure S))) - θ = 0
    rw [hunb, sub_self]
  rw [meanSquaredError_eq_variance_add_sq_bias hW, hb]
  simp

/-- Family unbiasedness makes family MSE equal variance at every parameter
with a finite second moment: a genuine predicate application. -/
theorem IsUnbiased.familyMeanSquaredError_eq_variance {Θ : Type*} {W : S → ℝ}
    {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ} (hunb : IsUnbiased W P τ)
    (hMem : ∀ θ, MemLp W 2 (((P θ)) : Measure S))
    (h2 : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) (((P θ)) : Measure S))
    (θ : Θ) :
    familyMeanSquaredError W P τ h2 θ =
      ProbabilityTheory.variance W (((P θ)) : Measure S) := by
  have h := familyMeanSquaredError_eq_variance_add_sq_familyBias hMem h2
    (fun θ => (hMem θ).integrable one_le_two) θ
  have hb : familyBias W P τ (fun θ => (hMem θ).integrable one_le_two) θ
      = 0 := by
    show (∫ x, W x ∂(((P θ)) : Measure S)) - τ θ = 0
    rw [hunb.expect_eq θ, sub_self]
  rw [h, hb]
  simp

/-- Source finite frequentist risk of one fixed rule: at each parameter, the
real expected loss under that parameter law and loss. `δ` is fixed before the
family and does not depend on `θ`; `A` may differ from `Θ`. The
per-parameter `Integrable` evidence is the source expectation domain from
Chapter 2 Definition 2.2.1; without it no finite source risk exists. No prior,
kernel, or optimality input occurs. Source equation 7.3.16. Blueprint
`af_36871388da7326a07a5e4f71`. -/
noncomputable def frequentistRisk {Θ A : Type*} (δ : S → A)
    (P : Θ → ProbabilityMeasure S) (ℓ : Θ → A → NNReal)
    (_h : ∀ θ, Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)) :
    Θ → ℝ :=
  fun θ => ∫ x, (ℓ θ (δ x) : ℝ) ∂((P θ) : Measure S)

/-- Exact value of finite frequentist risk at a parameter. -/
theorem frequentistRisk_apply {Θ A : Type*} {δ : S → A}
    {P : Θ → ProbabilityMeasure S} {ℓ : Θ → A → NNReal}
    {h : ∀ θ, Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)}
    (θ : Θ) :
    frequentistRisk δ P ℓ h θ =
      ∫ x, (ℓ θ (δ x) : ℝ) ∂((P θ) : Measure S) :=
  rfl

/-- Finite frequentist risk is nonnegative at every parameter. -/
theorem frequentistRisk_nonneg {Θ A : Type*} {δ : S → A}
    {P : Θ → ProbabilityMeasure S} {ℓ : Θ → A → NNReal}
    {h : ∀ θ, Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)}
    (θ : Θ) : 0 ≤ frequentistRisk δ P ℓ h θ := by
  unfold frequentistRisk
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => NNReal.coe_nonneg _)

/-- Extended risk bridge: nonnegative extended integral of the finite NNReal
cost. This is a boundary-analysis object only. It is not the source finite
risk; on the integrable domain it agrees with the source value by
`ofReal_frequentistRisk`, and off that domain with measurability it records
infinity by `frequentistRiskENN_eq_top_of_not_integrable`. Blueprint
`af_36871388da7326a07a5e4f71`. -/
noncomputable def frequentistRiskENN {Θ A : Type*} (δ : S → A)
    (P : Θ → ProbabilityMeasure S) (ℓ : Θ → A → NNReal) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ x, ℓ θ (δ x) ∂((P θ) : Measure S)

/-- On the finite domain, the extended bridge agrees with the source finite
risk value. Blueprint `af_36871388da7326a07a5e4f71`. -/
theorem ofReal_frequentistRisk {Θ A : Type*} {δ : S → A}
    {P : Θ → ProbabilityMeasure S} {ℓ : Θ → A → NNReal}
    {h : ∀ θ, Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)}
    (θ : Θ) :
    ENNReal.ofReal (frequentistRisk δ P ℓ h θ) =
      frequentistRiskENN δ P ℓ θ := by
  unfold frequentistRisk frequentistRiskENN
  exact (lintegral_coe_eq_integral (fun x => ℓ θ (δ x)) (h θ)).symm

/-- Off the finite domain, with measurability, the extended bridge records
infinity rather than a finite value. This prevents totalized-integral zero
from manufacturing finite risk. No off-domain finite value is claimed.
Blueprint `af_36871388da7326a07a5e4f71`. -/
theorem frequentistRiskENN_eq_top_of_not_integrable {Θ A : Type*}
    {δ : S → A} {P : Θ → ProbabilityMeasure S} {ℓ : Θ → A → NNReal}
    {θ : Θ}
    (hm : AEStronglyMeasurable (fun x => (ℓ θ (δ x) : ℝ))
      ((P θ) : Measure S))
    (h : ¬ Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)) :
    frequentistRiskENN δ P ℓ θ = ∞ := by
  have hnn : 0 ≤ᵐ[((P θ) : Measure S)] (fun x => (ℓ θ (δ x) : ℝ)) :=
    Filter.Eventually.of_forall fun x => NNReal.coe_nonneg _
  have hiff := lintegral_ofReal_ne_top_iff_integrable hm hnn
  have htop : ∫⁻ x, ENNReal.ofReal ((ℓ θ (δ x) : ℝ)) ∂((P θ) : Measure S)
      = ∞ := by
    by_contra hne
    exact h (hiff.mp hne)
  unfold frequentistRiskENN
  calc ∫⁻ x, (ℓ θ (δ x) : ℝ≥0∞) ∂((P θ) : Measure S)
        = ∫⁻ x, ENNReal.ofReal ((ℓ θ (δ x) : ℝ)) ∂((P θ) : Measure S) := by
          refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact ENNReal.ofReal_coe_nnreal.symm
      _ = ∞ := htop

/-- Finite family MSE is the squared-loss specialization of finite
frequentist risk. This reuses the accepted `familyMeanSquaredError` leaf;
it does not duplicate or change that MSE definition. Blueprint
`af_36871388da7326a07a5e4f71`. -/
theorem frequentistRisk_squared_eq_familyMeanSquaredError {Θ : Type*}
    {W : S → ℝ} {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ}
    (hRisk : ∀ θ, Integrable
      (fun x => ((⟨(W x - τ θ) ^ 2, sq_nonneg _⟩ : NNReal) : ℝ))
      (((P θ)) : Measure S))
    (hMSE : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) (((P θ)) : Measure S)) :
    frequentistRisk W P (fun θ a => ⟨(a - τ θ) ^ 2, sq_nonneg _⟩) hRisk =
      familyMeanSquaredError W P τ hMSE :=
  rfl

end

end MathlibExt.Probability.Statistics.EstimationRisk
