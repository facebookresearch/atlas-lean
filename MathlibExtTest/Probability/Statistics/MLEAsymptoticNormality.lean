/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MLEAsymptoticNormality
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Moments.Variance

/-!
# Tests for asymptotic normality of maximum likelihood

* Non-vacuity: the Gaussian location family `p θ = N(θ, 1)` (density with respect to Lebesgue
  measure) at `θ₀ = 0` satisfies every hypothesis of
  `tendstoInDistribution_sqrt_mul_sub_maximumLikelihood`, with score `x - θ`, Fisher information
  `1`, envelope `M = 0`, and the sample mean as the exact root of the likelihood equation, on
  the i.i.d. product space `ℕ → ℝ`. The theorem gives `√n · X̄ₙ → N(0, 1)`.
* The general convergence lemmas on concrete inputs.
* Boundary: outside the domain `p > 0`, a zero density has the junk score `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Statistics.FisherInformation
open MathlibExt.Probability.Statistics.MLEAsymptoticNormality

namespace MathlibExtTest.Probability.Statistics.MLEAsymptoticNormality

/-- The Gaussian location family `N(θ, 1)`. -/
noncomputable def pG (θ x : ℝ) : ℝ := gaussianPDFReal θ 1 x

/-- The Gaussian densities are positive. -/
theorem pG_pos (θ x : ℝ) : 0 < pG θ x := gaussianPDFReal_pos _ _ _ one_ne_zero

/-- The law with density `pG θ` is `N(θ, 1)`. -/
theorem lawOf_pG (θ : ℝ) : lawOf volume pG θ = gaussianReal θ 1 := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  rfl

/-- The log-density of `N(θ, 1)`. -/
theorem log_pG (θ x : ℝ) :
    Real.log (pG θ x) = Real.log (√(2 * Real.pi))⁻¹ - (x - θ) ^ 2 / 2 := by
  have h : 0 < (√(2 * Real.pi))⁻¹ := by positivity
  simp only [pG, gaussianPDFReal, NNReal.coe_one, mul_one]
  rw [Real.log_mul h.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- The score of the Gaussian location family is `x - θ`. -/
theorem score_pG (θ x : ℝ) : score pG θ x = x - θ := by
  have e : (fun t => Real.log (pG t x)) =
      fun t => Real.log (√(2 * Real.pi))⁻¹ - (x - t) ^ 2 / 2 := funext fun t => log_pG t x
  have h : HasDerivAt (fun t => Real.log (√(2 * Real.pi))⁻¹ - (x - t) ^ 2 / 2) (x - θ) θ := by
    have h1 : HasDerivAt (fun t => x - t) (-1) θ := by
      simpa using (hasDerivAt_id θ).const_sub x
    have h3 := ((h1.mul h1).div_const 2).const_sub (Real.log (√(2 * Real.pi))⁻¹)
    convert h3 using 1
    · funext t; simp only [Pi.mul_apply]; ring
    · ring
  rw [score, e, h.deriv]

/-- The score as a function of the parameter. -/
theorem score_pG_fun (x : ℝ) : (fun t => score pG t x) = fun t => x - t :=
  funext fun t => score_pG t x

/-- The derivative of the score is `-1`. -/
theorem deriv_score_pG (x θ : ℝ) : deriv (fun t => score pG t x) θ = -1 := by
  rw [score_pG_fun]
  simp

/-- The second derivative of the score vanishes (envelope `M = 0`). -/
theorem deriv_deriv_score_pG (x θ : ℝ) :
    deriv (fun t => deriv (fun s => score pG s x) t) θ = 0 := by
  simp_rw [deriv_score_pG]
  exact deriv_const θ (-1)

/-- The log-density is differentiable in the parameter. -/
theorem differentiableAt_log_pG (x θ : ℝ) :
    DifferentiableAt ℝ (fun t => Real.log (pG t x)) θ := by
  have e : (fun t => Real.log (pG t x)) =
      fun t => Real.log (√(2 * Real.pi))⁻¹ - (x - t) ^ 2 / 2 := funext fun t => log_pG t x
  rw [e]; fun_prop

/-- The density is differentiable in the parameter. -/
theorem differentiableAt_pG (x θ : ℝ) : DifferentiableAt ℝ (fun t => pG t x) θ := by
  have e : (fun t => pG t x) = fun t => Real.exp (Real.log (pG t x)) :=
    funext fun t => (Real.exp_log (pG_pos t x)).symm
  rw [e]; exact (differentiableAt_log_pG x θ).exp

/-- The Fisher information of `N(θ, 1)` at `0` is `1`. -/
theorem fisherInformation_pG : fisherInformation volume pG 0 = 1 := by
  rw [← integral_score_sq (fun x => pG_pos 0 x) (measurable_gaussianPDFReal 0 1)
    (fun x => differentiableAt_pG x 0), lawOf_pG]
  simp only [score_pG, sub_zero]
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero aemeasurable_id integral_id_gaussianReal] at h
  simpa using h

/-- The i.i.d. sample space: coordinates of the infinite product of `N(0, 1)`. -/
noncomputable def sampleG : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1

instance : IsProbabilityMeasure sampleG := by unfold sampleG; infer_instance

/-- The sample mean, the root of the likelihood equation of the Gaussian location family. -/
noncomputable def sampleMean (n : ℕ) (ω : ℕ → ℝ) : ℝ := (∑ i ∈ Finset.range n, ω i) / n

/-- Each coordinate of the sample has law `N(0, 1)`. -/
theorem hasLaw_coord (i : ℕ) : HasLaw (fun ω : ℕ → ℝ => ω i) (lawOf volume pG 0) sampleG := by
  rw [lawOf_pG]
  exact ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

/-- The coordinates of the sample are independent. -/
theorem iIndepFun_coord : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) sampleG :=
  iIndepFun_infinitePi (P := fun _ => gaussianReal 0 1) (X := fun _ => id)
    (fun _ => measurable_id)

/-- The sample mean solves the likelihood equation for every `n` (including `n = 0`). -/
theorem sum_score_sampleMean (n : ℕ) (ω : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, score pG (sampleMean n ω) (ω i) = 0 := by
  simp only [score_pG, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    sampleMean]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · field_simp; ring

/-- The sample mean is consistent (strong law). -/
theorem tendstoInMeasure_sampleMean :
    TendstoInMeasure sampleG sampleMean atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
  · exact ((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).div_const _
      ).aestronglyMeasurable
  · have h := strong_law_ae_real (fun i (ω : ℕ → ℝ) => ω i)
      ((hasLaw_coord 0).integrable_comp (f := id) (by
        rw [lawOf_pG]; exact (memLp_id_gaussianReal 1).integrable le_rfl))
      (fun i j hij => iIndepFun_coord.indepFun hij)
      (fun i => ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
        ((hasLaw_coord i).map_eq.trans (hasLaw_coord 0).map_eq.symm)⟩)
    have h0 : ∫ ω, ω 0 ∂sampleG = 0 := by
      have := (hasLaw_coord 0).integral_comp (f := id) aestronglyMeasurable_id
      simp only [Function.comp_def, id, lawOf_pG] at this
      rw [this, integral_id_gaussianReal]
    rw [h0] at h
    exact h

/-- **Non-vacuity of `tendstoInDistribution_sqrt_mul_sub_maximumLikelihood`**: for the Gaussian
location family every hypothesis holds, and the theorem yields `√n · X̄ₙ → N(0, 1)`. -/
theorem tendstoInDistribution_sqrt_mul_sampleMean :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (sampleMean n ω - 0)) atTop id
      (fun _ => sampleG) (gaussianReal 0 1) := by
  have hmeas : ∀ n, Measurable (sampleMean n) := fun n =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).div_const _
  have hY : HasLaw id (gaussianReal 0 (fisherInformation volume pG 0)⁻¹.toNNReal)
      (gaussianReal 0 1) := by
    rw [fisherInformation_pG, inv_one, Real.toNNReal_one]; exact HasLaw.id
  have hroot : ∀ n, {ω : ℕ → ℝ | ∑ i ∈ Finset.range n, score pG (sampleMean n ω) (ω i) ≠ 0} =
      ∅ := fun n => by
    ext ω; simp [sum_score_sampleMean]
  have hsq : Integrable (fun x => score pG 0 x ^ 2) (lawOf volume pG 0) := by
    simp only [score_pG, sub_zero, lawOf_pG]
    exact (memLp_id_gaussianReal 2).integrable_sq
  have hmean : ∫ x, score pG 0 x ∂lawOf volume pG 0 = 0 := by
    simp only [score_pG, sub_zero, lawOf_pG]; exact integral_id_gaussianReal
  have hlaw : IsProbabilityMeasure (lawOf volume pG 0) := by rw [lawOf_pG]; infer_instance
  have hinfo : ∫ x, deriv (fun t => score pG t x) 0 ∂lawOf volume pG 0 =
      -fisherInformation volume pG 0 := by
    simp [deriv_score_pG, fisherInformation_pG]
  exact tendstoInDistribution_sqrt_mul_sub_maximumLikelihood (δ := 1) (M := fun _ => 0)
    one_pos pG_pos (measurable_gaussianPDFReal 0 1) hasLaw_coord iIndepFun_coord
    (fun x θ _ => differentiableAt_log_pG x θ) (fun x θ _ => by rw [score_pG_fun]; fun_prop)
    (fun x θ _ => by simp_rw [deriv_score_pG]; fun_prop) measurable_const
    (integrable_zero _ _ _) (fun x θ _ => by rw [deriv_deriv_score_pG, abs_zero])
    (by rw [show score pG 0 = fun x => x - 0 from funext fun x => score_pG 0 x]; fun_prop)
    hsq hmean (by simp_rw [deriv_score_pG]; fun_prop)
    (by simp_rw [deriv_score_pG]; exact integrable_const (-1 : ℝ)) hinfo
    (by rw [fisherInformation_pG]; exact one_pos) (fun n => (hmeas n).aemeasurable)
    (by simp_rw [hroot, measure_empty]; exact tendsto_const_nhds) tendstoInMeasure_sampleMean hY

/-- Convergence in distribution to a constant gives convergence in probability (a constant
sequence). -/
example : TendstoInMeasure sampleG (fun (_ : ℕ) (_ : ℕ → ℝ) => (3 : ℝ)) atTop (fun _ => 3) :=
  tendstoInMeasure_of_tendstoInDistribution_const (P' := sampleG)
    (tendstoInDistribution_const aemeasurable_const)

/-- The domination lemma with full events and a zero bound. -/
example : TendstoInMeasure sampleG (fun (_ : ℕ) (_ : ℕ → ℝ) => (0 : ℝ)) atTop 0 :=
  tendstoInMeasure_zero_of_abs_le (V := fun _ _ => 0) (G := fun _ => Set.univ)
    (by rw [tendstoInMeasure_iff_norm]; intro ε hε; simp [hε.not_ge])
    (by simp) (fun _ _ _ => by simp)

/-- Boundary (junk value): outside the domain `p > 0`, the zero density has score `0`, because
`Real.log 0 = 0`. The theorems above all assume `0 < p θ x`. -/
example (θ x : ℝ) : score (fun _ (_ : ℝ) => (0 : ℝ)) θ x = 0 := by
  simp [score]

#print axioms tendstoInDistribution_sqrt_mul_sampleMean

end MathlibExtTest.Probability.Statistics.MLEAsymptoticNormality
