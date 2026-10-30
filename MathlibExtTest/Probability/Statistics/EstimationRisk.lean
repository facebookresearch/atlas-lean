/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.EstimationRisk
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Tests for estimation risk: bias, mean squared error, and unbiasedness

Positive cases use a genuine fair two-point law, a full Bernoulli family, and
Dirac laws with a fixed estimator. The MSE decomposition is verified
numerically on laws with nonzero bias and variance. Negative cases exhibit a
genuine infinite-moment geometric law, reject zero and infinite sampling
measures as probability laws, and record empty-domain vacuity explicitly.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Topology

open MathlibExt.Probability.Statistics.EstimationRisk

namespace EstimationRiskTest

/-- Fixed nonconstant real estimator on a two-point sample space. -/
def twoPointW : Bool → ℝ
  | false => 0
  | true => 1

/-- Fair two-point law as a PMF. -/
noncomputable def twoPointP : PMF Bool :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2 : ℝ)) (by
    simp only [Fintype.univ_bool,
      Finset.sum_insert (show true ∉ ({false} : Finset Bool) from by decide),
      Finset.sum_singleton]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      show (1 / 2 : ℝ) + 1 / 2 = 1 from by norm_num, ENNReal.ofReal_one])

/-- The fair two-point law as a probability measure. -/
noncomputable def twoPointμ : ProbabilityMeasure Bool :=
  ⟨twoPointP.toMeasure, inferInstance⟩

/-- Expected value of the fixed estimator under the fair two-point law. -/
theorem twoPoint_integral :
    ∫ b, twoPointW b ∂(twoPointμ : Measure Bool) = (1 / 2 : ℝ) := by
  have hμ : (twoPointμ : Measure Bool) = twoPointP.toMeasure := rfl
  rw [hμ, PMF.integral_eq_sum]
  simp only [Fintype.univ_bool,
    Finset.sum_insert (show true ∉ ({false} : Finset Bool) from by decide),
    Finset.sum_singleton, twoPointP, PMF.ofFintype_apply]
  rw [show twoPointW true = (1 : ℝ) from rfl,
    show twoPointW false = (0 : ℝ) from rfl,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp [smul_eq_mul]

/-- The fixed estimator is genuinely nonconstant. -/
example : twoPointW false ≠ twoPointW true := by
  show (0 : ℝ) ≠ 1
  norm_num

/-- Both points carry mass: this is a genuine two-point law. -/
example : false ∈ twoPointP.support ∧ true ∈ twoPointP.support := by
  have hpos : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  simp only [PMF.mem_support_iff, twoPointP, PMF.ofFintype_apply]
  exact ⟨hpos, hpos⟩

/-- Bias of the fixed estimator at target `0` under the two-point law. -/
theorem twoPoint_bias :
    bias twoPointW twoPointμ 0 Integrable.of_finite = (1 / 2 : ℝ) := by
  rw [bias_eq_integral, twoPoint_integral, sub_zero]

/-- Nonzero bias: the fixed nonconstant estimator is biased at target `0`. -/
example : bias twoPointW twoPointμ 0 Integrable.of_finite ≠ 0 := by
  rw [twoPoint_bias]
  norm_num

/-- Finite MSE of the fixed estimator at target `0` under the two-point law. -/
theorem twoPoint_mse :
    meanSquaredError twoPointW twoPointμ 0 Integrable.of_finite
      = (1 / 2 : ℝ) := by
  have hsq : ∀ b : Bool, (twoPointW b - 0) ^ 2 = twoPointW b := by
    intro b
    cases b
    · show ((0 : ℝ) - 0) ^ 2 = 0
      norm_num
    · show ((1 : ℝ) - 0) ^ 2 = 1
      norm_num
  rw [meanSquaredError_eq_integral,
    integral_congr_ae (Filter.Eventually.of_forall hsq)]
  exact twoPoint_integral

/-- Positive MSE for the fixed nonconstant estimator at target `0`. -/
example : 0 < meanSquaredError twoPointW twoPointμ 0 Integrable.of_finite := by
  rw [twoPoint_mse]
  norm_num

/-- A single fixed estimator serves every parameter of a nonempty family. -/
example (θ : Bool) :
    familyBias twoPointW (fun _ => twoPointμ) (fun _ => 0)
        (fun _ => Integrable.of_finite) θ = (1 / 2 : ℝ) := by
  simp only [familyBias_apply, twoPoint_integral, sub_zero]

/-- Family finite MSE on a nonempty parameter type with a fixed estimator. -/
example (θ : Bool) :
    familyMeanSquaredError twoPointW (fun _ => twoPointμ) (fun _ => 0)
        (fun _ => Integrable.of_finite) θ = (1 / 2 : ℝ) := by
  simp only [familyMeanSquaredError_apply]
  have hsq : ∀ b : Bool, (twoPointW b - (0 : ℝ)) ^ 2 = twoPointW b := by
    intro b
    cases b
    · show ((0 : ℝ) - 0) ^ 2 = 0
      norm_num
    · show ((1 : ℝ) - 0) ^ 2 = 1
      norm_num
  rw [integral_congr_ae (Filter.Eventually.of_forall hsq)]
  exact twoPoint_integral

/-- Dirac laws are probability laws. -/
example (a : Bool) : IsProbabilityMeasure (Measure.dirac a) :=
  Measure.dirac.isProbabilityMeasure

/-- Dirac boundary: bias is evaluation minus target. -/
example (W : Bool → ℝ) (a : Bool) (θ : ℝ)
    (hW : Integrable W ((diracProba a : ProbabilityMeasure Bool) : Measure Bool)) :
    bias W (diracProba a) θ hW = W a - θ := by
  have hcoe : ((diracProba a : ProbabilityMeasure Bool) : Measure Bool)
      = Measure.dirac a := rfl
  rw [bias_eq_integral, hcoe, integral_dirac]

/-- Dirac boundary: finite MSE is squared error at the support point. -/
example (W : Bool → ℝ) (a : Bool) (θ : ℝ)
    (hW2 : Integrable (fun x => (W x - θ) ^ 2)
      ((diracProba a : ProbabilityMeasure Bool) : Measure Bool)) :
    meanSquaredError W (diracProba a) θ hW2 = (W a - θ) ^ 2 := by
  have hcoe : ((diracProba a : ProbabilityMeasure Bool) : Measure Bool)
      = Measure.dirac a := rfl
  rw [meanSquaredError_eq_integral, hcoe, integral_dirac]

/-- Boundary Dirac law with constructed integrability evidence: bias is the
estimator value minus the target. -/
example (a θ : ℝ) :
    bias id ⟨Measure.dirac a, inferInstance⟩ θ
        (integrable_dirac (by simp)) = a - θ := by
  have h1 :=
    bias_eq_integral id (⟨Measure.dirac a, inferInstance⟩ : ProbabilityMeasure ℝ) θ
      (integrable_dirac (by simp))
  have h2 :
      ∫ x, id x ∂((⟨Measure.dirac a, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ)
        = a :=
    integral_dirac _ _
  exact h1.trans (congrArg (· - θ) h2)

/-- Boundary Dirac law with constructed integrability evidence: MSE is the
squared error at the support point. -/
example (a θ : ℝ) :
    meanSquaredError id ⟨Measure.dirac a, inferInstance⟩ θ
        (integrable_dirac (by simp)) = (a - θ) ^ 2 := by
  have h1 :=
    meanSquaredError_eq_integral id (⟨Measure.dirac a, inferInstance⟩ : ProbabilityMeasure ℝ) θ
      (integrable_dirac (by simp))
  have h2 :
      ∫ x, (id x - θ) ^ 2
          ∂((⟨Measure.dirac a, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ)
        = (a - θ) ^ 2 :=
    integral_dirac _ _
  exact h1.trans h2

/-- A constant estimator exactly at its target has MSE exactly `0`. -/
example (S : Type*) [MeasurableSpace S] (μ : ProbabilityMeasure S) (c : ℝ) :
    meanSquaredError (fun _ => c) μ c
      (by
        have h0 : ∀ x : S, (0 : ℝ) = ((fun _ => c) x - c) ^ 2 :=
          fun x => by norm_num
        exact (integrable_const (0 : ℝ)).congr
          (Filter.Eventually.of_forall h0)) = 0 := by
  have h0 : ∀ x : S, ((fun _ => c) x - c) ^ 2 = (0 : ℝ) :=
    fun x => by norm_num
  show ∫ x, ((fun _ => c) x - c) ^ 2 ∂(μ : Measure S) = 0
  rw [integral_congr_ae (Filter.Eventually.of_forall h0)]
  simp

/-- Constant zero estimator at target zero has exact zero MSE. -/
example : meanSquaredError (fun _ : Bool => (0 : ℝ)) (diracProba true) 0
    Integrable.of_finite = 0 := by
  have h0 : ∀ x : Bool, ((fun _ : Bool => (0 : ℝ)) x - 0) ^ 2 = (0 : ℝ) :=
    fun x => by norm_num
  show ∫ x, ((fun _ : Bool => (0 : ℝ)) x - 0) ^ 2
    ∂((diracProba true : ProbabilityMeasure Bool) : Measure Bool) = 0
  rw [integral_congr_ae (Filter.Eventually.of_forall h0)]
  simp

/-- The zero measure is not a probability law. -/
example (Ω : Type*) [MeasurableSpace Ω] :
    ¬ IsProbabilityMeasure (0 : Measure Ω) := by
  intro h
  have h1 := h.measure_univ
  have h0 : (0 : Measure Ω) Set.univ = 0 := rfl
  rw [h0] at h1
  exact zero_ne_one h1

/-- An infinite-mass scaled Dirac measure is not a probability law. -/
example (Ω : Type*) [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (a : Ω) :
    ¬ IsProbabilityMeasure ((∞ : ℝ≥0∞) • Measure.dirac a) := by
  intro h
  have h1 := h.measure_univ
  rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ a),
    smul_eq_mul, mul_one] at h1
  exact ENNReal.one_ne_top h1.symm

/-- Any infinite-mass measure fails to be a probability law. -/
example {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (hinf : μ Set.univ = ∞) : ¬ IsProbabilityMeasure μ := by
  intro hprob
  have huniv := hprob.measure_univ
  rw [hinf] at huniv
  exact ENNReal.one_ne_top huniv.symm

/-- Every probability law has total mass one. -/
example {S : Type*} [MeasurableSpace S] (μ : ProbabilityMeasure S) :
    (μ : Measure S) Set.univ = 1 :=
  μ.property.measure_univ

/-- Over an empty parameter type there is no nonzero-bias instance: vacuity,
not a positive claim. -/
example (S : Type*) [MeasurableSpace S] (W : S → ℝ)
    (P : Empty → ProbabilityMeasure S) (τ : Empty → ℝ)
    (h : ∀ θ, Integrable W ↑(P θ)) :
    ¬ ∃ θ : Empty, familyBias W P τ h θ ≠ 0 := fun ⟨θ, _⟩ => nomatch θ

/-- Over an empty parameter type there is no positive-MSE instance: vacuity,
not a positive claim. -/
example (S : Type*) [MeasurableSpace S] (W : S → ℝ)
    (P : Empty → ProbabilityMeasure S) (τ : Empty → ℝ)
    (h : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) ↑(P θ)) :
    ¬ ∃ θ : Empty, 0 < familyMeanSquaredError W P τ h θ :=
  fun ⟨θ, _⟩ => nomatch θ

/-- No probability law exists on an empty sample space. -/
example (Ω : Type*) [MeasurableSpace Ω] [IsEmpty Ω] (μ : Measure Ω) :
    ¬ IsProbabilityMeasure μ := by
  intro h
  have h1 := h.measure_univ
  rw [Set.univ_eq_empty_iff.mpr inferInstance, measure_empty] at h1
  exact zero_ne_one h1

/-- The type of probability laws on an empty sample space is empty. -/
example (Ω : Type*) [MeasurableSpace Ω] [IsEmpty Ω] :
    ¬ Nonempty (ProbabilityMeasure Ω) := by
  rintro ⟨⟨μ, hμ⟩⟩
  have h1 := hμ.measure_univ
  rw [Set.univ_eq_empty_iff.mpr inferInstance, measure_empty] at h1
  exact zero_ne_one h1

/-- Geometric half success probability in the unit interval. -/
noncomputable def geomHalf : unitInterval :=
  ⟨(1 / 2 : ℝ), Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩

/-- The geometric half parameter is nonzero. -/
theorem geomHalf_ne_zero : geomHalf ≠ 0 := by
  have h12 : ((geomHalf : unitInterval) : ℝ) = 1 / 2 := rfl
  intro h
  have hcoe : ((geomHalf : unitInterval) : ℝ) = 0 := by rw [h]; rfl
  rw [h12] at hcoe
  norm_num at hcoe

/-- Geometric half law is a probability law. -/
example : IsProbabilityMeasure
    (ProbabilityTheory.geometricMeasure geomHalf) :=
  inferInstance

/-- Constant one is not summable over the naturals. -/
theorem not_summable_one_nat : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro hsum
  have htend0 := hsum.tendsto_cofinite_zero
  have htend1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.cofinite (nhds 1) :=
    tendsto_const_nhds
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique htend1 htend0
  norm_num at h10

/-- Doubling estimator has infinite absolute moment under the geometric half
law, so it fails the finite-bias domain gate. -/
theorem geom_abs_notIntegrable :
    ¬ Integrable (fun n : ℕ => (2 : ℝ) ^ (n + 1))
      (ProbabilityTheory.geometricMeasure geomHalf) := by
  rw [ProbabilityTheory.integrable_geometricMeasure_iff geomHalf_ne_zero]
  have hone : (fun n : ℕ => (1 - ((geomHalf : unitInterval) : ℝ)) ^ n *
      ((geomHalf : unitInterval) : ℝ) * ‖(2 : ℝ) ^ (n + 1)‖)
      = fun _ : ℕ => (1 : ℝ) := by
    funext n
    have hp : ((geomHalf : unitInterval) : ℝ) = 1 / 2 := rfl
    rw [hp]
    have hnorm : ‖(2 : ℝ) ^ (n + 1)‖ = (2 : ℝ) ^ (n + 1) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm]
    have h2 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [h2, pow_add, pow_one]
    have hmul : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    calc (1 / 2 : ℝ) ^ n * (1 / 2) * ((2 : ℝ) ^ n * 2)
        = ((1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n) * ((1 / 2 : ℝ) * 2) := by ring
      _ = 1 * 1 := by rw [hmul]; norm_num
      _ = 1 := by norm_num
  rw [hone]
  exact not_summable_one_nat

/-- Doubling estimator has infinite square moment under the geometric half law
at target zero, so it fails the finite-MSE domain gate. -/
theorem geom_sq_notIntegrable :
    ¬ Integrable (fun n : ℕ => ((2 : ℝ) ^ (n + 1) - 0) ^ 2)
      (ProbabilityTheory.geometricMeasure geomHalf) := by
  rw [ProbabilityTheory.integrable_geometricMeasure_iff geomHalf_ne_zero]
  have hform : (fun n : ℕ => (1 - ((geomHalf : unitInterval) : ℝ)) ^ n *
      ((geomHalf : unitInterval) : ℝ) *
      ‖((2 : ℝ) ^ (n + 1) - 0) ^ 2‖)
      = fun n : ℕ => (2 : ℝ) ^ (n + 1) := by
    funext n
    have hp : ((geomHalf : unitInterval) : ℝ) = 1 / 2 := rfl
    rw [hp]
    have hsq : ((2 : ℝ) ^ (n + 1) - 0) ^ 2 = (2 : ℝ) ^ (2 * (n + 1)) := by
      rw [sub_zero, ← pow_mul, mul_comm (n + 1) 2]
    have hnorm : ‖((2 : ℝ) ^ (n + 1) - 0) ^ 2‖
        = (2 : ℝ) ^ (2 * (n + 1)) := by
      rw [hsq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm]
    have h2 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [h2]
    have hmul : (1 / 2 : ℝ) ^ n * (1 / 2) * (2 : ℝ) ^ (2 * (n + 1))
        = (2 : ℝ) ^ (n + 1) := by
      have hpow2 : (2 : ℝ) ^ (2 * (n + 1)) = ((2 : ℝ) ^ (n + 1)) ^ 2 := by
        rw [mul_comm 2 (n + 1), pow_mul]
      have hhalf : (1 / 2 : ℝ) ^ n * (1 / 2) = ((2 : ℝ) ^ (n + 1))⁻¹ := by
        have h1 : (1 / 2 : ℝ) ^ n * (1 / 2) = (1 / 2 : ℝ) ^ (n + 1) := by
          rw [pow_add, pow_one]
        rw [h1, div_pow, one_pow, one_div]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
      rw [hpow2, hhalf, pow_two, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    exact hmul
  rw [hform]
  intro hsum
  have hsum1 : Summable (fun _ : ℕ => (1 : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun _ => by norm_num) _ hsum
    intro n
    exact one_le_pow₀ (by norm_num)
  exact not_summable_one_nat hsum1

/-- Genuine infinite-moment estimator fails both finite gates and has infinite
extended squared error under the geometric half law at target zero. -/
example :
    ¬ Integrable (fun n : ℕ => (2 : ℝ) ^ (n + 1))
        (((ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure :
          ProbabilityMeasure ℕ) : Measure ℕ) ∧
    ¬ Integrable (fun n : ℕ => ((fun m : ℕ => (2 : ℝ) ^ (m + 1)) n - 0) ^ 2)
        (((ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure :
          ProbabilityMeasure ℕ) : Measure ℕ) ∧
    meanSquaredErrorENN (fun n : ℕ => (2 : ℝ) ^ (n + 1))
      (ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure
      0 = ∞ := by
  have hcoe : ((((ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure :
      ProbabilityMeasure ℕ)) : Measure ℕ)
      = ProbabilityTheory.geometricMeasure geomHalf := rfl
  have hAbs : ¬ Integrable (fun n : ℕ => (2 : ℝ) ^ (n + 1))
      (((ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure :
        ProbabilityMeasure ℕ) : Measure ℕ) := by
    rw [hcoe]
    exact geom_abs_notIntegrable
  have hSq : ¬ Integrable
      (fun n : ℕ => ((fun m : ℕ => (2 : ℝ) ^ (m + 1)) n - 0) ^ 2)
      (((ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure :
        ProbabilityMeasure ℕ) : Measure ℕ) := by
    have hfun : (fun n : ℕ => ((fun m : ℕ => (2 : ℝ) ^ (m + 1)) n - 0) ^ 2)
        = fun n : ℕ => ((2 : ℝ) ^ (n + 1) - 0) ^ 2 := rfl
    rw [hfun, hcoe]
    exact geom_sq_notIntegrable
  have hMeas : AEStronglyMeasurable
      (fun n : ℕ => ((fun m : ℕ => (2 : ℝ) ^ (m + 1)) n - (0 : ℝ)) ^ 2)
      (((ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure :
        ProbabilityMeasure ℕ) : Measure ℕ) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hTop : meanSquaredErrorENN (fun n : ℕ => (2 : ℝ) ^ (n + 1))
      (ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure
      0 = ∞ :=
    meanSquaredErrorENN_eq_top_of_not_finite hMeas hSq
  exact ⟨hAbs, hSq, hTop⟩

/-- Bernoulli family over the unit interval: mass `p` on `true`, `1 - p` on
`false`. -/
noncomputable def bernoulliP : unitInterval → ProbabilityMeasure Bool :=
  fun p => ⟨ProbabilityTheory.bernoulliMeasure true false p, inferInstance⟩

/-- The fixed 0/1 estimator has expectation `p` under the Bernoulli law:
derived from the Bernoulli integral, never assumed. -/
theorem bernoulli_integral (p : unitInterval) :
    ∫ b, twoPointW b ∂((bernoulliP p : ProbabilityMeasure Bool) : Measure Bool)
      = (p : ℝ) := by
  have hcoe : ((bernoulliP p : ProbabilityMeasure Bool) : Measure Bool)
      = ProbabilityTheory.bernoulliMeasure true false p := rfl
  rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
  show (p : ℝ) • twoPointW true + (1 - (p : ℝ)) • twoPointW false = (p : ℝ)
  show (p : ℝ) • (1 : ℝ) + (1 - (p : ℝ)) • (0 : ℝ) = (p : ℝ)
  simp [smul_eq_mul]

/-- The fixed 0/1 estimator is integrable under every Bernoulli law. -/
theorem bernoulli_integrable (p : unitInterval) :
    Integrable twoPointW
      ((bernoulliP p : ProbabilityMeasure Bool) : Measure Bool) := by
  have hcoe : ((bernoulliP p : ProbabilityMeasure Bool) : Measure Bool)
      = ProbabilityTheory.bernoulliMeasure true false p := rfl
  rw [hcoe]
  exact ProbabilityTheory.integrable_bernoulliMeasure true false p twoPointW

/-- Positive unbiased instance: the fixed 0/1 estimator is unbiased for the
identity target across the full Bernoulli family. -/
theorem bernoulli_isUnbiased :
    IsUnbiased twoPointW bernoulliP (fun p => (p : ℝ)) := by
  intro p
  exact ⟨bernoulli_integrable p, bernoulli_integral p⟩

/-- The Bernoulli parameter family is nonempty. -/
example : Nonempty unitInterval :=
  ⟨⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩⟩

/-- The Bernoulli target is genuinely nonconstant across the family. -/
example : ∃ p q : unitInterval, (p : ℝ) ≠ (q : ℝ) := by
  refine ⟨⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩,
    ⟨1, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩, ?_⟩
  show (0 : ℝ) ≠ (1 : ℝ)
  norm_num

/-- Boundary `p = 0`: expectation is exactly `0`. -/
example :
    ∫ b, twoPointW b ∂((bernoulliP
      ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ :
      ProbabilityMeasure Bool) : Measure Bool) = 0 :=
  bernoulli_integral _

/-- Boundary `p = 1`: expectation is exactly `1`. -/
example :
    ∫ b, twoPointW b ∂((bernoulliP
      ⟨1, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ :
      ProbabilityMeasure Bool) : Measure Bool) = 1 :=
  bernoulli_integral _

/-- Target value `0` is attained at the `p = 0` endpoint. -/
example : (fun p : unitInterval => (p : ℝ))
    ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ = 0 := rfl

/-- Unbiasedness makes the Bernoulli family bias vanish everywhere. -/
example (p : unitInterval) :
    familyBias twoPointW bernoulliP (fun q => (q : ℝ))
        (fun q => bernoulli_integrable q) p = 0 :=
  (isUnbiased_iff_forall_familyBias_eq_zero _).mp bernoulli_isUnbiased p

/-- Unbiased Bernoulli family has MSE equal to variance at every parameter. -/
example (p : unitInterval) :
    familyMeanSquaredError twoPointW bernoulliP (fun q => (q : ℝ))
        (fun _ => integrable_sq_sub_of_memLp_two MemLp.of_discrete) p
      = ProbabilityTheory.variance twoPointW
          ((bernoulliP p : ProbabilityMeasure Bool) : Measure Bool) :=
  bernoulli_isUnbiased.familyMeanSquaredError_eq_variance
    (fun _ => MemLp.of_discrete) _ p

/-- Constant zero is not unbiased for a nonzero target. -/
example : ¬ IsUnbiased (fun _ : Bool => (0 : ℝ)) (fun _ : Bool => twoPointμ)
    (fun _ : Bool => (1 : ℝ)) := by
  intro h
  obtain ⟨_, hexp⟩ := h true
  simp at hexp

/-- The totalized integral of the doubling estimator under the geometric half
law is `0`: nonintegrability makes the integral junk. -/
example : ∫ n : ℕ, (2 : ℝ) ^ (n + 1)
    ∂(ProbabilityTheory.geometricMeasure geomHalf) = 0 :=
  integral_undef geom_abs_notIntegrable

/-- A nonintegrable estimator is not unbiased even when the totalized integral
matches a zero target. -/
example : ¬ IsUnbiased (fun n : ℕ => (2 : ℝ) ^ (n + 1))
    (fun _ : Unit =>
      (ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure)
    (fun _ => 0) := by
  intro h
  obtain ⟨hint, _⟩ := h ()
  have hcoe : ((((ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure :
      ProbabilityMeasure ℕ)) : Measure ℕ)
      = ProbabilityTheory.geometricMeasure geomHalf := rfl
  rw [hcoe] at hint
  exact geom_abs_notIntegrable hint

/-- Over an empty parameter type every estimator is vacuously unbiased: this
is vacuity, not a positive claim. -/
example (W : Bool → ℝ) (P : Empty → ProbabilityMeasure Bool)
    (τ : Empty → ℝ) : IsUnbiased W P τ :=
  fun θ => nomatch θ

/-- Variance of the fixed estimator under the fair two-point law. -/
theorem twoPoint_variance :
    ProbabilityTheory.variance twoPointW
      ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)
      = (1 / 4 : ℝ) := by
  have hfun : ∀ b : Bool, (twoPointW ^ 2) b = twoPointW b := by
    intro b
    cases b
    · rw [Pi.pow_apply]
      show ((0 : ℝ) ^ 2) = 0
      norm_num
    · rw [Pi.pow_apply]
      show ((1 : ℝ) ^ 2) = 1
      norm_num
  have hsq : ∫ b, (twoPointW ^ 2) b
      ∂((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)
      = (1 / 2 : ℝ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
    exact twoPoint_integral
  have hmem : MemLp twoPointW 2
      ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool) :=
    MemLp.of_discrete
  have hvar := ProbabilityTheory.variance_eq_sub
    (μ := ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)) hmem
  rw [hsq, twoPoint_integral] at hvar
  rw [hvar]
  norm_num

/-- Headline decomposition on the fair law at target `0`: nonzero bias and
nonzero variance, `1/2 = 1/4 + (1/2)²`. -/
example : meanSquaredError twoPointW twoPointμ 0 Integrable.of_finite
    = ProbabilityTheory.variance twoPointW
        ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)
      + (bias twoPointW twoPointμ 0 Integrable.of_finite) ^ 2 := by
  rw [twoPoint_mse, twoPoint_variance, twoPoint_bias]
  norm_num

/-- Bias of the fixed estimator at nonzero target `1` under the fair law. -/
theorem twoPoint_bias_one :
    bias twoPointW twoPointμ 1 Integrable.of_finite = (-1 / 2 : ℝ) := by
  show (∫ b, twoPointW b
      ∂((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)) - 1 = _
  rw [twoPoint_integral]
  norm_num

/-- Finite MSE of the fixed estimator at nonzero target `1` under the fair
law, computed directly from the two-point law. -/
theorem twoPoint_mse_one :
    meanSquaredError twoPointW twoPointμ 1 Integrable.of_finite
      = (1 / 2 : ℝ) := by
  have hμ : ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)
      = twoPointP.toMeasure := rfl
  show ∫ b, (twoPointW b - 1) ^ 2
      ∂((twoPointμ : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [hμ, PMF.integral_eq_sum]
  simp only [Fintype.univ_bool,
    Finset.sum_insert (show true ∉ ({false} : Finset Bool) from by decide),
    Finset.sum_singleton, twoPointP, PMF.ofFintype_apply]
  rw [show (twoPointW true - 1) ^ 2 = (0 : ℝ) from by norm_num [twoPointW],
    show (twoPointW false - 1) ^ 2 = (1 : ℝ) from by norm_num [twoPointW],
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp [smul_eq_mul]

/-- Decomposition at nonzero target `1`: `1/2 = 1/4 + (-1/2)²`. -/
example : meanSquaredError twoPointW twoPointμ 1 Integrable.of_finite
    = ProbabilityTheory.variance twoPointW
        ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)
      + (bias twoPointW twoPointμ 1 Integrable.of_finite) ^ 2 := by
  rw [twoPoint_mse_one, twoPoint_variance, twoPoint_bias_one]
  norm_num

/-- Bias of the fixed estimator at negative target `-1` under the fair law. -/
theorem twoPoint_bias_neg_one :
    bias twoPointW twoPointμ (-1) Integrable.of_finite = (3 / 2 : ℝ) := by
  show (∫ b, twoPointW b
      ∂((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)) - (-1) = _
  rw [twoPoint_integral]
  norm_num

/-- Finite MSE of the fixed estimator at negative target `-1`: `5/2`. -/
theorem twoPoint_mse_neg_one :
    meanSquaredError twoPointW twoPointμ (-1) Integrable.of_finite
      = (5 / 2 : ℝ) := by
  have hμ : ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)
      = twoPointP.toMeasure := rfl
  show ∫ b, (twoPointW b - (-1)) ^ 2
      ∂((twoPointμ : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [hμ, PMF.integral_eq_sum]
  simp only [Fintype.univ_bool,
    Finset.sum_insert (show true ∉ ({false} : Finset Bool) from by decide),
    Finset.sum_singleton, twoPointP, PMF.ofFintype_apply]
  rw [show (twoPointW true - (-1)) ^ 2 = (4 : ℝ) from by norm_num [twoPointW],
    show (twoPointW false - (-1)) ^ 2 = (1 : ℝ) from by norm_num [twoPointW],
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp only [smul_eq_mul]
  norm_num

/-- Decomposition at negative target `-1`: `5/2 = 1/4 + (3/2)²`. -/
example : meanSquaredError twoPointW twoPointμ (-1) Integrable.of_finite
    = ProbabilityTheory.variance twoPointW
        ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)
      + (bias twoPointW twoPointμ (-1) Integrable.of_finite) ^ 2 := by
  rw [twoPoint_mse_neg_one, twoPoint_variance, twoPoint_bias_neg_one]
  norm_num

/-- Dirac laws have exactly zero variance for the fixed estimator. -/
theorem dirac_variance_zero (a : Bool) :
    ProbabilityTheory.variance twoPointW
      (((diracProba a : ProbabilityMeasure Bool)) : Measure Bool) = 0 := by
  have hcoe : (((diracProba a : ProbabilityMeasure Bool)) : Measure Bool)
      = Measure.dirac a := rfl
  have hmeas : AEMeasurable twoPointW (Measure.dirac a) :=
    (measurable_of_countable _).aemeasurable
  have hvar := ProbabilityTheory.variance_eq_integral
    (X := twoPointW) (μ := Measure.dirac a) hmeas
  rw [hcoe, hvar]
  have hmean : ∫ b, twoPointW b ∂(Measure.dirac a) = twoPointW a :=
    integral_dirac _ _
  rw [hmean, integral_dirac, sub_self]
  norm_num

/-- Decomposition on Dirac laws at any real target: squared error equals zero
variance plus squared bias. -/
example (a : Bool) (θ : ℝ) :
    meanSquaredError twoPointW (diracProba a) θ Integrable.of_finite
      = ProbabilityTheory.variance twoPointW
          (((diracProba a : ProbabilityMeasure Bool)) : Measure Bool)
        + (bias twoPointW (diracProba a) θ Integrable.of_finite) ^ 2 := by
  have hcoe : (((diracProba a : ProbabilityMeasure Bool)) : Measure Bool)
      = Measure.dirac a := rfl
  have hmse : meanSquaredError twoPointW (diracProba a) θ Integrable.of_finite
      = (twoPointW a - θ) ^ 2 := by
    show ∫ b, (twoPointW b - θ) ^ 2
        ∂(((diracProba a : ProbabilityMeasure Bool)) : Measure Bool) = _
    rw [hcoe, integral_dirac]
  have hbias : bias twoPointW (diracProba a) θ Integrable.of_finite
      = twoPointW a - θ := by
    show (∫ b, twoPointW b
        ∂(((diracProba a : ProbabilityMeasure Bool)) : Measure Bool)) - θ = _
    rw [hcoe, integral_dirac]
  rw [hmse, hbias, dirac_variance_zero]
  ring

/-- The doubling estimator fails the decomposition's finite-moment gate under
the geometric half law. -/
example : ¬ MemLp (fun n : ℕ => (2 : ℝ) ^ (n + 1)) 2
    (ProbabilityTheory.geometricMeasure geomHalf) := by
  intro hmem
  exact geom_abs_notIntegrable (hmem.integrable one_le_two)

/-- The extended bridge records the `ofReal` of the decomposed value on the
fair law at target `0`. -/
example : ENNReal.ofReal (ProbabilityTheory.variance twoPointW
        ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)
      + (bias twoPointW twoPointμ 0 Integrable.of_finite) ^ 2)
    = meanSquaredErrorENN twoPointW twoPointμ 0 :=
  ofReal_variance_add_sq_bias MemLp.of_discrete

/-- Quarter success probability in the unit interval. -/
noncomputable def q14 : unitInterval :=
  ⟨(1 / 4 : ℝ), Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩

/-- Three-quarter success probability in the unit interval. -/
noncomputable def q34 : unitInterval :=
  ⟨(3 / 4 : ℝ), Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩

/-- Real labels for the two-parameter risk model. -/
def riskTau : Bool → ℝ
  | false => 0
  | true => 1

/-- Squared-error NNReal loss at the two-parameter labels. -/
def riskSqLoss : Bool → ℝ → NNReal :=
  fun θ a => ⟨(a - riskTau θ) ^ 2, sq_nonneg _⟩

/-- Two-parameter Bernoulli family: success `1/4` at `false`, `1/2` at `true`. -/
noncomputable def riskP : Bool → ProbabilityMeasure Bool
  | false => bernoulliP q14
  | true => bernoulliP geomHalf

/-- Replacement family: success `3/4` at `true`, unchanged at `false`. -/
noncomputable def riskP34 : Bool → ProbabilityMeasure Bool
  | false => bernoulliP q14
  | true => bernoulliP q34

/-- Squared cost at label `0` integrates to the success probability. -/
theorem riskSq_integral_zero (p : unitInterval) :
    ∫ b, ((riskSqLoss false (twoPointW b)) : ℝ)
      ∂((bernoulliP p : ProbabilityMeasure Bool) : Measure Bool)
      = (p : ℝ) := by
  have hcoe : ((bernoulliP p : ProbabilityMeasure Bool) : Measure Bool)
      = ProbabilityTheory.bernoulliMeasure true false p := rfl
  rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
  have htrue : ((riskSqLoss false (twoPointW true)) : ℝ) = (1 : ℝ) := by
    show ((1 : ℝ) - 0) ^ 2 = 1
    norm_num
  have hfalse : ((riskSqLoss false (twoPointW false)) : ℝ) = (0 : ℝ) := by
    show ((0 : ℝ) - 0) ^ 2 = 0
    norm_num
  rw [htrue, hfalse]
  simp [smul_eq_mul]

/-- Squared cost at label `1` integrates to one minus the success probability. -/
theorem riskSq_integral_one (p : unitInterval) :
    ∫ b, ((riskSqLoss true (twoPointW b)) : ℝ)
      ∂((bernoulliP p : ProbabilityMeasure Bool) : Measure Bool)
      = 1 - (p : ℝ) := by
  have hcoe : ((bernoulliP p : ProbabilityMeasure Bool) : Measure Bool)
      = ProbabilityTheory.bernoulliMeasure true false p := rfl
  rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
  have htrue : ((riskSqLoss true (twoPointW true)) : ℝ) = (0 : ℝ) := by
    show ((1 : ℝ) - 1) ^ 2 = 0
    norm_num
  have hfalse : ((riskSqLoss true (twoPointW false)) : ℝ) = (1 : ℝ) := by
    show ((0 : ℝ) - 1) ^ 2 = 1
    norm_num
  rw [htrue, hfalse]
  simp [smul_eq_mul]

/-- Risk at label `0` under success `1/4` is `1/4`. -/
theorem riskP_false_risk :
    frequentistRisk twoPointW riskP riskSqLoss
        (fun _ => Integrable.of_finite) false = (1 / 4 : ℝ) := by
  rw [frequentistRisk_apply]
  show ∫ b, ((riskSqLoss false (twoPointW b)) : ℝ)
    ∂((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [riskSq_integral_zero]
  rfl

/-- Risk at label `1` under success `1/2` is `1/2`. -/
theorem riskP_true_risk :
    frequentistRisk twoPointW riskP riskSqLoss
        (fun _ => Integrable.of_finite) true = (1 / 2 : ℝ) := by
  rw [frequentistRisk_apply]
  show ∫ b, ((riskSqLoss true (twoPointW b)) : ℝ)
    ∂((bernoulliP geomHalf : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [riskSq_integral_one]
  have hp : ((geomHalf : unitInterval) : ℝ) = 1 / 2 := rfl
  rw [hp]
  norm_num

/-- Varying-family bias at `false`: expectation `1/4` minus target `0`. -/
theorem riskP_false_bias :
    familyBias twoPointW riskP riskTau (fun _ => Integrable.of_finite) false
      = (1 / 4 : ℝ) := by
  rw [familyBias_apply]
  show (∫ b, twoPointW b
      ∂((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool)) - 0 = _
  rw [bernoulli_integral]
  have hp : ((q14 : unitInterval) : ℝ) = 1 / 4 := rfl
  rw [hp, sub_zero]

/-- Varying-family MSE at `false`: squared error at label `0` is `1/4`. -/
theorem riskP_false_mse :
    familyMeanSquaredError twoPointW riskP riskTau
        (fun _ => Integrable.of_finite) false = (1 / 4 : ℝ) := by
  rw [familyMeanSquaredError_apply]
  show ∫ b, ((riskSqLoss false (twoPointW b)) : ℝ)
    ∂((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [riskSq_integral_zero]
  rfl

/-- Varying-family bias at `true`: expectation `1/2` minus target `1`. -/
theorem riskP_true_bias :
    familyBias twoPointW riskP riskTau (fun _ => Integrable.of_finite) true
      = (-1 / 2 : ℝ) := by
  rw [familyBias_apply]
  show (∫ b, twoPointW b
      ∂((bernoulliP geomHalf : ProbabilityMeasure Bool) : Measure Bool)) - 1
      = _
  rw [bernoulli_integral]
  have hp : ((geomHalf : unitInterval) : ℝ) = 1 / 2 := rfl
  rw [hp]
  norm_num

/-- Varying-family MSE at `true`: squared error at label `1` is `1/2`. -/
theorem riskP_true_mse :
    familyMeanSquaredError twoPointW riskP riskTau
        (fun _ => Integrable.of_finite) true = (1 / 2 : ℝ) := by
  rw [familyMeanSquaredError_apply]
  show ∫ b, ((riskSqLoss true (twoPointW b)) : ℝ)
    ∂((bernoulliP geomHalf : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [riskSq_integral_one]
  have hp : ((geomHalf : unitInterval) : ℝ) = 1 / 2 := rfl
  rw [hp]
  norm_num

/-- Replacing the `true` law by success `3/4` changes only its risk to `1/4`. -/
theorem riskP34_true_risk :
    frequentistRisk twoPointW riskP34 riskSqLoss
        (fun _ => Integrable.of_finite) true = (1 / 4 : ℝ) := by
  rw [frequentistRisk_apply]
  show ∫ b, ((riskSqLoss true (twoPointW b)) : ℝ)
    ∂((bernoulliP q34 : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [riskSq_integral_one]
  show 1 - ((q34 : unitInterval) : ℝ) = _
  have hp : ((q34 : unitInterval) : ℝ) = 3 / 4 := rfl
  rw [hp]
  norm_num

/-- The `false` risk is unchanged by the `true`-only replacement. -/
theorem riskP34_false_risk :
    frequentistRisk twoPointW riskP34 riskSqLoss
        (fun _ => Integrable.of_finite) false = (1 / 4 : ℝ) := by
  rw [frequentistRisk_apply]
  show ∫ b, ((riskSqLoss false (twoPointW b)) : ℝ)
    ∂((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [riskSq_integral_zero]
  rfl

/-- Fixed constant-zero rule. -/
def constZeroW : Bool → ℝ := fun _ => 0

/-- Fixed constant-one rule. -/
def constOneW : Bool → ℝ := fun _ => 1

/-- Crossing laws: success `1/4` at `false`, `3/4` at `true`. -/
noncomputable def riskCrossP : Bool → ProbabilityMeasure Bool
  | false => bernoulliP q14
  | true => bernoulliP q34

/-- Constant-zero risks cross as `(0, 1)`. -/
theorem constZero_risks :
    frequentistRisk constZeroW riskCrossP riskSqLoss
          (fun _ => Integrable.of_finite) false = 0 ∧
      frequentistRisk constZeroW riskCrossP riskSqLoss
          (fun _ => Integrable.of_finite) true = 1 := by
  constructor
  · rw [frequentistRisk_apply]
    have h0 : ∀ b : Bool, ((riskSqLoss false (constZeroW b)) : ℝ) = 0 := by
      intro b
      show ((0 : ℝ) - 0) ^ 2 = 0
      norm_num
    rw [integral_congr_ae (Filter.Eventually.of_forall h0)]
    simp
  · rw [frequentistRisk_apply]
    have h1 : ∀ b : Bool, ((riskSqLoss true (constZeroW b)) : ℝ) = 1 := by
      intro b
      show ((0 : ℝ) - 1) ^ 2 = 1
      norm_num
    rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
    show ∫ _ : Bool, (1 : ℝ)
      ∂((bernoulliP q34 : ProbabilityMeasure Bool) : Measure Bool) = _
    have hcoe : ((bernoulliP q34 : ProbabilityMeasure Bool) : Measure Bool)
        = ProbabilityTheory.bernoulliMeasure true false q34 := rfl
    rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
    have hp : ((q34 : unitInterval) : ℝ) = 3 / 4 := rfl
    rw [hp]
    simp only [smul_eq_mul]
    norm_num

/-- Constant-one risks cross as `(1, 0)`. -/
theorem constOne_risks :
    frequentistRisk constOneW riskCrossP riskSqLoss
          (fun _ => Integrable.of_finite) false = 1 ∧
      frequentistRisk constOneW riskCrossP riskSqLoss
          (fun _ => Integrable.of_finite) true = 0 := by
  constructor
  · rw [frequentistRisk_apply]
    have h1 : ∀ b : Bool, ((riskSqLoss false (constOneW b)) : ℝ) = 1 := by
      intro b
      show ((1 : ℝ) - 0) ^ 2 = 1
      norm_num
    rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
    show ∫ _ : Bool, (1 : ℝ)
      ∂((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool) = _
    have hcoe : ((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool)
        = ProbabilityTheory.bernoulliMeasure true false q14 := rfl
    rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
    have hp : ((q14 : unitInterval) : ℝ) = 1 / 4 := rfl
    rw [hp]
    simp only [smul_eq_mul]
    norm_num
  · rw [frequentistRisk_apply]
    have h0 : ∀ b : Bool, ((riskSqLoss true (constOneW b)) : ℝ) = 0 := by
      intro b
      show ((1 : ℝ) - 1) ^ 2 = 0
      norm_num
    rw [integral_congr_ae (Filter.Eventually.of_forall h0)]
    simp

/-- No universal best-estimator claim is stored: the two constant risks cross. -/
example :
    frequentistRisk constZeroW riskCrossP riskSqLoss
          (fun _ => Integrable.of_finite) false <
        frequentistRisk constOneW riskCrossP riskSqLoss
          (fun _ => Integrable.of_finite) false ∧
      frequentistRisk constOneW riskCrossP riskSqLoss
          (fun _ => Integrable.of_finite) true <
        frequentistRisk constZeroW riskCrossP riskSqLoss
          (fun _ => Integrable.of_finite) true := by
  obtain ⟨hz0, hz1⟩ := constZero_risks
  obtain ⟨ho0, ho1⟩ := constOne_risks
  rw [hz0, ho0, ho1, hz1]
  norm_num

/-- Finite NNReal loss with `A = Bool` independent of real `Θ`: unequal cells. -/
def boolLossR : ℝ → Bool → NNReal :=
  fun θ a => ⟨(match a with | true => (1 : ℝ) | false => 0) + θ ^ 2, by
    cases a <;> positivity⟩

/-- Dirac at `false`: risk `0` at `θ = 0`, risk `1` at `θ = 1`. -/
theorem boolLossR_dirac_false :
    frequentistRisk id (fun _ : ℝ => diracProba false) boolLossR
          (fun _ => Integrable.of_finite) 0 = 0 ∧
      frequentistRisk id (fun _ : ℝ => diracProba false) boolLossR
          (fun _ => Integrable.of_finite) 1 = 1 := by
  constructor
  · rw [frequentistRisk_apply]
    have hcoe : ((diracProba false : ProbabilityMeasure Bool) : Measure Bool)
        = Measure.dirac false := rfl
    show ∫ b, ((boolLossR 0 b) : ℝ)
      ∂((diracProba false : ProbabilityMeasure Bool) : Measure Bool) = _
    rw [hcoe, integral_dirac]
    show (0 : ℝ) + (0 : ℝ) ^ 2 = 0
    norm_num
  · rw [frequentistRisk_apply]
    have hcoe : ((diracProba false : ProbabilityMeasure Bool) : Measure Bool)
        = Measure.dirac false := rfl
    show ∫ b, ((boolLossR 1 b) : ℝ)
      ∂((diracProba false : ProbabilityMeasure Bool) : Measure Bool) = _
    rw [hcoe, integral_dirac]
    show (0 : ℝ) + (1 : ℝ) ^ 2 = 1
    norm_num

/-- Dirac at `true`: positive unequal risks `1` and `2`. -/
theorem boolLossR_dirac_true :
    frequentistRisk id (fun _ : ℝ => diracProba true) boolLossR
          (fun _ => Integrable.of_finite) 0 = 1 ∧
      frequentistRisk id (fun _ : ℝ => diracProba true) boolLossR
          (fun _ => Integrable.of_finite) 1 = 2 := by
  constructor
  · rw [frequentistRisk_apply]
    have hcoe : ((diracProba true : ProbabilityMeasure Bool) : Measure Bool)
        = Measure.dirac true := rfl
    show ∫ b, ((boolLossR 0 b) : ℝ)
      ∂((diracProba true : ProbabilityMeasure Bool) : Measure Bool) = _
    rw [hcoe, integral_dirac]
    show (1 : ℝ) + (0 : ℝ) ^ 2 = 1
    norm_num
  · rw [frequentistRisk_apply]
    have hcoe : ((diracProba true : ProbabilityMeasure Bool) : Measure Bool)
        = Measure.dirac true := rfl
    show ∫ b, ((boolLossR 1 b) : ℝ)
      ∂((diracProba true : ProbabilityMeasure Bool) : Measure Bool) = _
    rw [hcoe, integral_dirac]
    show (1 : ℝ) + (1 : ℝ) ^ 2 = 2
    norm_num

/-- Bernoulli `1/4`: risks `1/4` at `θ = 0` and `5/4` at `θ = 1`. -/
theorem boolLossR_bernoulli :
    frequentistRisk id (fun _ : ℝ => bernoulliP q14) boolLossR
          (fun _ => Integrable.of_finite) 0 = (1 / 4 : ℝ) ∧
      frequentistRisk id (fun _ : ℝ => bernoulliP q14) boolLossR
          (fun _ => Integrable.of_finite) 1 = (5 / 4 : ℝ) := by
  constructor
  · rw [frequentistRisk_apply]
    have hcoe : ((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool)
        = ProbabilityTheory.bernoulliMeasure true false q14 := rfl
    show ∫ b, ((boolLossR 0 b) : ℝ)
      ∂((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool) = _
    rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
    have htrue : ((boolLossR 0 true) : ℝ) = (1 : ℝ) := by
      show (1 : ℝ) + (0 : ℝ) ^ 2 = 1
      norm_num
    have hfalse : ((boolLossR 0 false) : ℝ) = (0 : ℝ) := by
      show (0 : ℝ) + (0 : ℝ) ^ 2 = 0
      norm_num
    have hp : ((q14 : unitInterval) : ℝ) = 1 / 4 := rfl
    rw [htrue, hfalse, hp]
    simp [smul_eq_mul]
  · rw [frequentistRisk_apply]
    have hcoe : ((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool)
        = ProbabilityTheory.bernoulliMeasure true false q14 := rfl
    show ∫ b, ((boolLossR 1 b) : ℝ)
      ∂((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool) = _
    rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
    have htrue : ((boolLossR 1 true) : ℝ) = (2 : ℝ) := by
      show (1 : ℝ) + (1 : ℝ) ^ 2 = 2
      norm_num
    have hfalse : ((boolLossR 1 false) : ℝ) = (1 : ℝ) := by
      show (0 : ℝ) + (1 : ℝ) ^ 2 = 1
      norm_num
    have hp : ((q14 : unitInterval) : ℝ) = 1 / 4 := rfl
    rw [htrue, hfalse, hp]
    simp only [smul_eq_mul]
    norm_num

/-- Wrong-law family: both parameters use the `1/4` law. -/
noncomputable def riskPwrong : Bool → ProbabilityMeasure Bool
  | false => bernoulliP q14
  | true => bernoulliP q14

/-- Using the wrong parameter law changes the nonconstant risk to `3/4`. -/
theorem riskPwrong_true_risk :
    frequentistRisk twoPointW riskPwrong riskSqLoss
        (fun _ => Integrable.of_finite) true = (3 / 4 : ℝ) := by
  rw [frequentistRisk_apply]
  show ∫ b, ((riskSqLoss true (twoPointW b)) : ℝ)
    ∂((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [riskSq_integral_one]
  show 1 - ((q14 : unitInterval) : ℝ) = _
  have hp : ((q14 : unitInterval) : ℝ) = 1 / 4 := rfl
  rw [hp]
  norm_num

/-- Wrong-law value differs from the correct-law value. -/
example :
    frequentistRisk twoPointW riskPwrong riskSqLoss
          (fun _ => Integrable.of_finite) true ≠
        frequentistRisk twoPointW riskP riskSqLoss
          (fun _ => Integrable.of_finite) true := by
  rw [riskPwrong_true_risk, riskP_true_risk]
  norm_num

/-- Swapped loss parameters: `false` uses the `true` loss and conversely. -/
def riskSqLossSwap : Bool → ℝ → NNReal
  | false, a => riskSqLoss true a
  | true, a => riskSqLoss false a

/-- Swapping the loss parameter changes the risk from `1/4` to `3/4`. -/
theorem riskSwap_false_risk :
    frequentistRisk twoPointW riskP riskSqLossSwap
        (fun _ => Integrable.of_finite) false = (3 / 4 : ℝ) := by
  rw [frequentistRisk_apply]
  have hcoe : ((riskP false : ProbabilityMeasure Bool) : Measure Bool)
      = ProbabilityTheory.bernoulliMeasure true false q14 := rfl
  show ∫ b, ((riskSqLossSwap false (twoPointW b)) : ℝ)
    ∂((riskP false : ProbabilityMeasure Bool) : Measure Bool) = _
  rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
  have htrue : ((riskSqLossSwap false (twoPointW true)) : ℝ) = (0 : ℝ) := by
    show ((1 : ℝ) - 1) ^ 2 = 0
    norm_num
  have hfalse : ((riskSqLossSwap false (twoPointW false)) : ℝ) = (1 : ℝ) := by
    show ((0 : ℝ) - 1) ^ 2 = 1
    norm_num
  have hp : ((q14 : unitInterval) : ℝ) = 1 / 4 := rfl
  rw [htrue, hfalse, hp]
  simp only [smul_eq_mul]
  norm_num

/-- Swapped-loss value differs from the correct-loss value. -/
example :
    frequentistRisk twoPointW riskP riskSqLossSwap
          (fun _ => Integrable.of_finite) false ≠
        frequentistRisk twoPointW riskP riskSqLoss
          (fun _ => Integrable.of_finite) false := by
  rw [riskSwap_false_risk, riskP_false_risk]
  norm_num

/-- Zero finite loss gives zero risk under every actual law. -/
example (θ : Bool) :
    frequentistRisk twoPointW riskP (fun _ _ => 0)
        (fun _ => Integrable.of_finite) θ = 0 := by
  rw [frequentistRisk_apply]
  have h0 : ∀ b : Bool, ((((fun _ _ => (0 : NNReal)) θ (twoPointW b))) : ℝ)
      = 0 := fun b => rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall h0)]
  simp

/-- Finite constant loss `2` gives risk `2` by probability normalization. -/
example (θ : Bool) :
    frequentistRisk twoPointW riskP
        (fun _ _ => NNReal.mk (2 : ℝ) (by norm_num))
        (fun _ => Integrable.of_finite) θ = 2 := by
  cases θ
  · rw [frequentistRisk_apply]
    have h2 : ∀ b : Bool,
        ((((fun _ _ => NNReal.mk (2 : ℝ) (by norm_num)) false
          (twoPointW b))) : ℝ) = 2 := fun b => rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall h2)]
    show ∫ _ : Bool, (2 : ℝ)
      ∂((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool) = _
    have hcoe : ((bernoulliP q14 : ProbabilityMeasure Bool) : Measure Bool)
        = ProbabilityTheory.bernoulliMeasure true false q14 := rfl
    rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
    have hp : ((q14 : unitInterval) : ℝ) = 1 / 4 := rfl
    rw [hp]
    simp only [smul_eq_mul]
    norm_num
  · rw [frequentistRisk_apply]
    have h2 : ∀ b : Bool,
        ((((fun _ _ => NNReal.mk (2 : ℝ) (by norm_num)) true
          (twoPointW b))) : ℝ) = 2 := fun b => rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall h2)]
    show ∫ _ : Bool, (2 : ℝ)
      ∂((bernoulliP geomHalf : ProbabilityMeasure Bool) : Measure Bool) = _
    have hcoe : ((bernoulliP geomHalf : ProbabilityMeasure Bool) : Measure Bool)
        = ProbabilityTheory.bernoulliMeasure true false geomHalf := rfl
    rw [hcoe, ProbabilityTheory.integral_bernoulliMeasure]
    have hp : ((geomHalf : unitInterval) : ℝ) = 1 / 2 := rfl
    rw [hp]
    simp only [smul_eq_mul]
    norm_num

/-- Doubling estimator on the naturals. -/
noncomputable def geomDouble : ℕ → ℝ := fun n => (2 : ℝ) ^ (n + 1)

/-- Squared loss at target `0` for the geometric boundary. -/
noncomputable def geomSqLoss : Unit → ℝ → NNReal :=
  fun _ a => ⟨(a - 0) ^ 2, sq_nonneg _⟩

/-- Geometric half family on a single parameter. -/
noncomputable def geomP : Unit → ProbabilityMeasure ℕ :=
  fun _ => (ProbabilityTheory.geometricMeasure geomHalf).toProbabilityMeasure

/-- The geometric squared cost is not integrable: finite pointwise NNReal
cost with no finite-risk evidence. Reuses the accepted MSE boundary proof. -/
theorem geomRisk_notIntegrable :
    ¬ Integrable (fun n => ((geomSqLoss () (geomDouble n)) : ℝ))
      (((geomP ()) : ProbabilityMeasure ℕ) : Measure ℕ) := by
  have hcoe : ((((geomP ()) : ProbabilityMeasure ℕ)) : Measure ℕ)
      = ProbabilityTheory.geometricMeasure geomHalf := rfl
  rw [hcoe]
  show ¬ Integrable (fun n : ℕ => ((2 : ℝ) ^ (n + 1) - 0) ^ 2) _
  exact geom_sq_notIntegrable

/-- The extended risk bridge preserves `∞` for the nonintegrable cost. -/
theorem geomRisk_top :
    frequentistRiskENN geomDouble geomP geomSqLoss () = ∞ :=
  frequentistRiskENN_eq_top_of_not_integrable
    (measurable_of_countable _).aestronglyMeasurable
    geomRisk_notIntegrable

/-- No finite-risk integrability evidence exists on this boundary. -/
example (h : ∀ θ : Unit, Integrable
    (fun n => ((geomSqLoss θ (geomDouble n)) : ℝ))
    (((geomP θ) : ProbabilityMeasure ℕ) : Measure ℕ)) : False :=
  geomRisk_notIntegrable (h ())

/-- Constant top ENNReal loss under a genuine probability law stays top. -/
example : ∫⁻ b, (∞ : ℝ≥0∞)
    ∂((twoPointμ : ProbabilityMeasure Bool) : Measure Bool) = ∞ := by
  have huniv : ((twoPointμ : ProbabilityMeasure Bool) : Measure Bool)
      Set.univ = 1 := twoPointμ.property.measure_univ
  rw [lintegral_const, huniv, mul_one]

/-- Finite NNReal values never equal top, so infinite loss cannot enter the
finite source loss type. -/
example (n : NNReal) : (n : ℝ≥0∞) ≠ ∞ :=
  ENNReal.coe_ne_top

/-- `toReal` maps top to junk zero; the finite risk API never uses it. -/
example : ENNReal.toReal (∞ : ℝ≥0∞) = 0 := rfl

/-- A negative real value cannot inhabit the nonnegative loss type. -/
example : ¬ ∃ n : NNReal, (n : ℝ) = (-1 : ℝ) := by
  rintro ⟨n, hn⟩
  have hnn : 0 ≤ (n : ℝ) := NNReal.coe_nonneg n
  rw [hn] at hnn
  norm_num at hnn

/-- Over an empty parameter type there is no nonzero-risk instance: vacuity,
not a positive claim. -/
example (S : Type*) [MeasurableSpace S] (A : Type*) (δ : S → A)
    (P : Empty → ProbabilityMeasure S) (ℓ : Empty → A → NNReal)
    (h : ∀ θ, Integrable (fun x => (ℓ θ (δ x) : ℝ)) ↑(P θ)) :
    ¬ ∃ θ : Empty, frequentistRisk δ P ℓ h θ ≠ 0 :=
  fun ⟨θ, _⟩ => nomatch θ

/-- No decision rule maps a nonempty sample into an empty action type. -/
example (S : Type*) [Nonempty S] (δ : S → Empty) : False := by
  obtain ⟨s⟩ := ‹Nonempty S›
  exact nomatch δ s

/-- Finite risk evaluates to its native integral. -/
example (θ : Bool) :
    frequentistRisk twoPointW riskP riskSqLoss
          (fun _ => Integrable.of_finite) θ =
        ∫ b, ((riskSqLoss θ (twoPointW b)) : ℝ)
          ∂(((riskP θ) : ProbabilityMeasure Bool) : Measure Bool) :=
  frequentistRisk_apply θ

/-- Finite risk is nonnegative. -/
example (θ : Bool) :
    0 ≤ frequentistRisk twoPointW riskP riskSqLoss
      (fun _ => Integrable.of_finite) θ :=
  frequentistRisk_nonneg θ

/-- The extended bridge agrees with the finite risk on its domain. -/
example (θ : Bool) :
    ENNReal.ofReal (frequentistRisk twoPointW riskP riskSqLoss
        (fun _ => Integrable.of_finite) θ) =
      frequentistRiskENN twoPointW riskP riskSqLoss θ :=
  ofReal_frequentistRisk θ

/-- Squared-loss risk agrees pointwise with the accepted family MSE leaf. -/
example (θ : Bool) :
    frequentistRisk twoPointW riskP riskSqLoss
          (fun _ => Integrable.of_finite) θ =
        familyMeanSquaredError twoPointW riskP riskTau
          (fun _ => Integrable.of_finite) θ :=
  congrFun (frequentistRisk_squared_eq_familyMeanSquaredError
    (W := twoPointW) (P := riskP) (τ := riskTau)
    (fun _ => Integrable.of_finite) (fun _ => Integrable.of_finite)) θ

end EstimationRiskTest
