/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.VectorInference
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw

/-!
# Tests for finite-dimensional Fisher information and regular likelihood inference

* Non-vacuity: the Gaussian location family `N(θ, Id)` on a finite-dimensional real inner
  product space `E`, written as the density `p θ x = exp(⟪θ, x⟫ - ‖θ‖² / 2)` with respect to the
  standard Gaussian `N(0, Id)`, has score `x - θ`, Fisher information `Id` at `θ₀ = 0`, envelope
  `M = 0`, and the sample mean as exact root of the likelihood equation. On the i.i.d. product
  space `ℕ → E` every hypothesis of the vector MLE, Wald, Rao and Wilks theorems holds; they
  give `√n X̄ₙ → N(0, Id)` and `χ²_d` limits for `n ‖X̄ₙ‖²`, `‖Sₙ‖²` and the likelihood ratio.
* `hasLaw_inner_inverse_chiSquare` with `S = 1`: `‖Z‖² ~ χ²_d` for `Z ~ N(0, Id)`.
* Boundary: a parameter-free family has zero score and zero (singular) information, so the
  directional Cramér–Rao bound forces `Dg(θ) u = 0`, and the nonsingularity hypothesis fails.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)
open MathlibExt.Probability.Statistics.VectorInference

namespace MathlibExtTest.Probability.Statistics.VectorInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Gaussian location family `N(θ, Id)` as a density with respect to `N(0, Id)`. -/
noncomputable def pE (θ x : E) : ℝ := Real.exp (⟪θ, x⟫ - ‖θ‖ ^ 2 / 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The log-density is `⟪θ, x⟫ - ‖θ‖² / 2`. -/
theorem log_pE (θ x : E) : Real.log (pE θ x) = ⟪θ, x⟫ - ‖θ‖ ^ 2 / 2 := Real.log_exp _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the log-density in `θ` is `v ↦ ⟪x - θ, v⟫`. -/
theorem hasFDerivAt_log_pE (θ x : E) :
    HasFDerivAt (fun t => Real.log (pE t x)) (innerSL ℝ (x - θ)) θ := by
  have e : (fun t => Real.log (pE t x)) = fun t => ⟪t, x⟫ - (1 / 2 : ℝ) * ‖t‖ ^ 2 := by
    funext t; rw [log_pE]; ring
  rw [e]
  have h1 : HasFDerivAt (fun t : E => ⟪t, x⟫) (innerSL ℝ x) θ := by
    have := (innerSL ℝ x).hasFDerivAt (x := θ)
    simpa [real_inner_comm] using this
  have h2 : HasFDerivAt (fun t : E => (1 / 2 : ℝ) * ‖t‖ ^ 2) (innerSL ℝ θ) θ := by
    have := (hasStrictFDerivAt_norm_sq θ).hasFDerivAt.const_mul (1 / 2 : ℝ)
    convert this using 1
    ext v; simp
  convert h1.sub h2 using 1
  ext v; simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- The score of the Gaussian location family is `x - θ`. -/
theorem score_pE (θ x : E) : score pE θ x = x - θ := by
  refine ext_inner_right ℝ fun v => ?_
  rw [score, inner_gradient_left, (hasFDerivAt_log_pE θ x).fderiv, innerSL_apply_apply]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the score is `-Id`. -/
theorem fderiv_score_pE (x θ : E) :
    fderiv ℝ (fun t => score pE t x) θ = -ContinuousLinearMap.id ℝ E := by
  simp_rw [score_pE]
  exact ((hasFDerivAt_id θ).const_sub x).fderiv

omit [BorelSpace E] in
/-- At `θ₀ = 0` the density is `1`, so the data law is the standard Gaussian. -/
theorem lawOf_pE : lawOf (stdGaussian E) pE 0 = stdGaussian E := by
  have : (fun x => ENNReal.ofReal (pE (0 : E) x)) = 1 := by
    funext x; simp [pE]
  rw [lawOf, this, withDensity_one]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The score at `0` is the identity. -/
theorem score_pE_zero : score pE (0 : E) = id := funext fun x => by simp [score_pE]

/-- The score at `0` is square integrable. -/
theorem memLp_score_pE : MemLp (score pE (0 : E)) 2 (lawOf (stdGaussian E) pE 0) := by
  rw [score_pE_zero, lawOf_pE]
  exact IsGaussian.memLp_two_id

/-- **Fisher information of the Gaussian location family**: `I(0) = Id`. -/
theorem fisherInformation_pE :
    fisherInformation (stdGaussian E) pE 0 = ContinuousLinearMap.id ℝ E := by
  ext u
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_fisherInformation_apply memLp_score_pE]
  simp_rw [score_pE, sub_zero, lawOf_pE]
  have h := covarianceBilin_apply (μ := stdGaussian E) IsGaussian.memLp_two_id u v
  have h' : ⟪u, v⟫ = ∫ z, ⟪u, z⟫ * ⟪v, z⟫ ∂(stdGaussian E) := by
    simp [covarianceBilin_stdGaussian, integral_id_stdGaussian, id] at h
    exact h
  show _ = ⟪u, v⟫
  rw [h']
  congr 1; funext z
  rw [real_inner_comm z u, real_inner_comm z v]

/-- The information `Id` is positive definite. -/
theorem fisherInformation_pE_pos (u : E) (hu : u ≠ 0) :
    0 < ⟪fisherInformation (stdGaussian E) pE 0 u, u⟫ := by
  rw [fisherInformation_pE, ContinuousLinearMap.id_apply]
  exact real_inner_self_pos.2 hu

/-- `Ring.inverse Id = Id`. -/
theorem inverse_fisherInformation_pE :
    Ring.inverse (fisherInformation (stdGaussian E) pE 0) = ContinuousLinearMap.id ℝ E := by
  rw [fisherInformation_pE, ← ContinuousLinearMap.one_def, Ring.inverse_one]

/-- The i.i.d. sample space: coordinates of the infinite product of `N(0, Id)`. -/
noncomputable def sampleE : Measure (ℕ → E) := Measure.infinitePi fun _ => stdGaussian E

instance : IsProbabilityMeasure (sampleE (E := E)) := by unfold sampleE; infer_instance

/-- The sample mean, the root of the likelihood equation. -/
noncomputable def sampleMean (n : ℕ) (ω : ℕ → E) : E := (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, ω i

omit [BorelSpace E] in
/-- Each coordinate of the sample has the data law `p 0 ν = N(0, Id)`. -/
theorem hasLaw_coord (i : ℕ) :
    HasLaw (fun ω : ℕ → E => ω i) (lawOf (stdGaussian E) pE 0) sampleE := by
  rw [lawOf_pE]
  exact ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

omit [BorelSpace E] in
/-- The coordinates of the sample are independent. -/
theorem iIndepFun_coord : iIndepFun (fun i (ω : ℕ → E) => ω i) sampleE :=
  iIndepFun_infinitePi (P := fun _ => stdGaussian E) (X := fun _ => id) (fun _ => measurable_id)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The sample mean solves the likelihood equation for every `n` (including `n = 0`). -/
theorem sum_score_sampleMean (n : ℕ) (ω : ℕ → E) :
    ∑ i ∈ Finset.range n, score pE (sampleMean n ω) (ω i) = 0 := by
  simp only [score_pE, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sampleMean]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'),
      one_smul, sub_self]

/-- The sample mean is measurable. -/
theorem measurable_sampleMean (n : ℕ) : Measurable (sampleMean (E := E) n) :=
  (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_smul _

/-- The sample mean is consistent (strong law). -/
theorem tendstoInMeasure_sampleMean :
    TendstoInMeasure sampleE (sampleMean (E := E)) atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_tendsto_ae (fun n => (measurable_sampleMean n).aestronglyMeasurable)
    ?_
  have h := strong_law_ae (fun i (ω : ℕ → E) => ω i)
    ((hasLaw_coord 0).integrable_comp (f := id) (by
      rw [lawOf_pE]; exact IsGaussian.integrable_id))
    (fun i j hij => iIndepFun_coord.indepFun hij)
    (fun i => ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      ((hasLaw_coord i).map_eq.trans (hasLaw_coord 0).map_eq.symm)⟩)
  have h0 : ∫ ω, ω 0 ∂(sampleE (E := E)) = 0 := by
    have := (hasLaw_coord (E := E) 0).integral_comp (f := id) aestronglyMeasurable_id
    simp only [Function.comp_def, id, lawOf_pE] at this
    rw [this, integral_id_stdGaussian]
  rw [h0] at h
  exact h

omit [BorelSpace E] in
/-- The likelihood-equation event fails with probability `0`. -/
theorem tendsto_root (θhat : ℕ → (ℕ → E) → E) (hθ : θhat = sampleMean) :
    Tendsto (fun n => sampleE {ω | ∑ i ∈ Finset.range n, score pE (θhat n ω) (ω i) ≠ 0})
      atTop (𝓝 0) := by
  subst hθ
  have h : ∀ n, {ω : ℕ → E | ∑ i ∈ Finset.range n, score pE (sampleMean n ω) (ω i) ≠ 0} = ∅ :=
    fun n => by ext ω; simp [sum_score_sampleMean]
  simp [h]

/-- The projections of the standard Gaussian are `N(0, ‖t‖²) = N(0, ⟪I(0)⁻¹ t, t⟫)`. -/
theorem hasLaw_inner_id (t : E) :
    HasLaw (fun z : E => ⟪id z, t⟫)
      (gaussianReal 0 (⟪Ring.inverse (fisherInformation (stdGaussian E) pE 0) t, t⟫).toNNReal)
      (stdGaussian E) := by
  rw [inverse_fisherInformation_pE, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  exact ⟨by fun_prop, map_inner_stdGaussian t⟩

/-- **Non-vacuity of `tendstoInDistribution_sqrt_smul_sub_of_likelihoodEquation`**: for the
Gaussian location family on `E` every hypothesis holds, and the theorem yields
`√n X̄ₙ → N(0, Id)`. -/
theorem tendstoInDistribution_sqrt_smul_sampleMean :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (sampleMean n ω - 0)) atTop id
      (fun _ => sampleE) (stdGaussian E) := by
  have hs : Integrable (fun x => ‖score pE (0 : E) x‖ ^ 2) (lawOf (stdGaussian E) pE 0) :=
    memLp_score_pE.integrable_norm_pow two_ne_zero
  have hmean : ∫ x, score pE (0 : E) x ∂(lawOf (stdGaussian E) pE 0) = 0 := by
    simp only [score_pE, sub_zero, lawOf_pE]; exact integral_id_stdGaussian
  have hD : (fun x : E => fderiv ℝ (fun t => score pE t x) 0) =
      fun _ => -ContinuousLinearMap.id ℝ E := funext fun x => fderiv_score_pE x 0
  have hlaw : IsProbabilityMeasure (lawOf (stdGaussian E) pE 0) := by
    rw [lawOf_pE]; infer_instance
  exact tendstoInDistribution_sqrt_smul_sub_of_likelihoodEquation (ν := stdGaussian E) (p := pE)
    (θ₀ := 0) (δ := 1)
    (M := fun _ => 0)
    one_pos hasLaw_coord iIndepFun_coord
    (fun x θ _ => by simp_rw [score_pE]; fun_prop) measurable_const (integrable_const _)
    (fun x θ _ => by rw [fderiv_score_pE, fderiv_score_pE]; simp)
    (by rw [score_pE_zero]; exact measurable_id) hs hmean
    (by rw [hD]; exact stronglyMeasurable_const) (by rw [hD]; exact integrable_const _)
    (by rw [hD, fisherInformation_pE]; simp)
    (by rw [fisherInformation_pE, ← ContinuousLinearMap.one_def]; exact isUnit_one)
    (fun n => (measurable_sampleMean n).aemeasurable) (tendsto_root _ rfl)
    tendstoInMeasure_sampleMean aemeasurable_id hasLaw_inner_id

/-- `hasLaw_inner_inverse_chiSquare` with `S = 1`: `‖Z‖² ~ χ²_d` for `Z ~ N(0, Id)`. -/
theorem hasLaw_chiSquare_id [Nontrivial E] :
    HasLaw (fun z : E => ⟪Ring.inverse (1 : E →L[ℝ] E) (id z), id z⟫)
      (chiSquareMeasure (Module.finrank ℝ E)) (stdGaussian E) :=
  hasLaw_inner_inverse_chiSquare (S := 1) (fun u v => rfl)
    (fun u hu => real_inner_self_pos.2 hu) Module.finrank_pos aemeasurable_id fun t => by
      refine ⟨by fun_prop, ?_⟩
      rw [show (1 : E →L[ℝ] E) t = t from rfl, real_inner_self_eq_norm_sq]
      exact map_inner_stdGaussian t

/-- The chi-square law with `d = dim E ≥ 1` degrees of freedom is a probability measure. -/
instance [Nontrivial E] : IsProbabilityMeasure (chiSquareMeasure (Module.finrank ℝ E)) :=
  isProbabilityMeasure_chiSquareMeasure Module.finrank_pos

/-- **Non-vacuity of `tendstoInDistribution_waldStatistic`**: `n ‖X̄ₙ‖² → χ²_d`. -/
theorem tendstoInDistribution_wald_sampleMean [Nontrivial E] :
    TendstoInDistribution
      (fun (n : ℕ) ω => n * ⟪fisherInformation (stdGaussian E) pE 0 (sampleMean n ω - 0),
        sampleMean n ω - 0⟫) atTop id (fun _ => sampleE)
      (chiSquareMeasure (Module.finrank ℝ E)) := by
  have hs : Integrable (fun x => ‖score pE (0 : E) x‖ ^ 2) (lawOf (stdGaussian E) pE 0) :=
    memLp_score_pE.integrable_norm_pow two_ne_zero
  have hmean : ∫ x, score pE (0 : E) x ∂(lawOf (stdGaussian E) pE 0) = 0 := by
    simp only [score_pE, sub_zero, lawOf_pE]; exact integral_id_stdGaussian
  have hD : (fun x : E => fderiv ℝ (fun t => score pE t x) 0) =
      fun _ => -ContinuousLinearMap.id ℝ E := funext fun x => fderiv_score_pE x 0
  have hlaw : IsProbabilityMeasure (lawOf (stdGaussian E) pE 0) := by
    rw [lawOf_pE]; infer_instance
  exact tendstoInDistribution_waldStatistic (ν := stdGaussian E) (p := pE) (θ₀ := 0) (δ := 1)
    (M := fun _ => 0)
    one_pos hasLaw_coord iIndepFun_coord
    (fun x θ _ => by simp_rw [score_pE]; fun_prop) measurable_const (integrable_const _)
    (fun x θ _ => by rw [fderiv_score_pE, fderiv_score_pE]; simp)
    (by rw [score_pE_zero]; exact measurable_id) hs hmean
    (by rw [hD]; exact stronglyMeasurable_const) (by rw [hD]; exact integrable_const _)
    (by rw [hD, fisherInformation_pE]; simp) fisherInformation_pE_pos Module.finrank_pos
    (fun n => (measurable_sampleMean n).aemeasurable) (tendsto_root _ rfl)
    tendstoInMeasure_sampleMean HasLaw.id

/-- **Non-vacuity of `tendstoInDistribution_scoreStatistic`**: `‖Sₙ‖² → χ²_d` with
`Sₙ = n^{-1/2} ∑_{i<n} X i`. -/
theorem tendstoInDistribution_score_sample [Nontrivial E] :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → E) =>
        ⟪Ring.inverse (fisherInformation (stdGaussian E) pE 0)
            ((√n)⁻¹ • ∑ i ∈ Finset.range n, score pE 0 (ω i)),
          (√n)⁻¹ • ∑ i ∈ Finset.range n, score pE 0 (ω i)⟫)
      atTop id (fun _ => sampleE) (chiSquareMeasure (Module.finrank ℝ E)) := by
  have hs : Integrable (fun x => ‖score pE (0 : E) x‖ ^ 2) (lawOf (stdGaussian E) pE 0) :=
    memLp_score_pE.integrable_norm_pow two_ne_zero
  have hmean : ∫ x, score pE (0 : E) x ∂(lawOf (stdGaussian E) pE 0) = 0 := by
    simp only [score_pE, sub_zero, lawOf_pE]; exact integral_id_stdGaussian
  exact tendstoInDistribution_scoreStatistic (ν := stdGaussian E) (p := pE) (θ₀ := 0)
    hasLaw_coord iIndepFun_coord
    (by rw [score_pE_zero]; exact measurable_id) hs hmean fisherInformation_pE_pos
    Module.finrank_pos
    HasLaw.id

/-- **Non-vacuity of `tendstoInDistribution_two_mul_logLikelihood_sub`** (Wilks): the
likelihood ratio `2 ∑_{i<n} (log p X̄ₙ (X i) - log p 0 (X i))` converges to `χ²_d`. -/
theorem tendstoInDistribution_wilks_sampleMean [Nontrivial E] :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → E) => 2 * ∑ i ∈ Finset.range n,
        (Real.log (pE (sampleMean n ω) (ω i)) - Real.log (pE 0 (ω i))))
      atTop id (fun _ => sampleE) (chiSquareMeasure (Module.finrank ℝ E)) := by
  have hs : Integrable (fun x => ‖score pE (0 : E) x‖ ^ 2) (lawOf (stdGaussian E) pE 0) :=
    memLp_score_pE.integrable_norm_pow two_ne_zero
  have hmean : ∫ x, score pE (0 : E) x ∂(lawOf (stdGaussian E) pE 0) = 0 := by
    simp only [score_pE, sub_zero, lawOf_pE]; exact integral_id_stdGaussian
  have hD : (fun x : E => fderiv ℝ (fun t => score pE t x) 0) =
      fun _ => -ContinuousLinearMap.id ℝ E := funext fun x => fderiv_score_pE x 0
  have hlaw : IsProbabilityMeasure (lawOf (stdGaussian E) pE 0) := by
    rw [lawOf_pE]; infer_instance
  exact tendstoInDistribution_two_mul_logLikelihood_sub (ν := stdGaussian E) (p := pE)
    (θ₀ := 0) (δ := 1)
    (M := fun _ => 0)
    one_pos (by unfold pE; fun_prop) hasLaw_coord iIndepFun_coord
    (fun x θ _ => (hasFDerivAt_log_pE θ x).differentiableAt)
    (fun x θ _ => by simp_rw [score_pE]; fun_prop) measurable_const (integrable_const _)
    (fun x θ _ => by rw [fderiv_score_pE, fderiv_score_pE]; simp)
    (by rw [score_pE_zero]; exact measurable_id) hs hmean
    (by rw [hD]; exact stronglyMeasurable_const) (by rw [hD]; exact integrable_const _)
    (by rw [hD, fisherInformation_pE]; simp) fisherInformation_pE_pos Module.finrank_pos
    (fun n => (measurable_sampleMean n).aemeasurable) (tendsto_root _ rfl)
    tendstoInMeasure_sampleMean HasLaw.id

/-! ### Basic API -/

/-- `⟪I(θ) u, u⟫` agrees with the scalar Fisher information of the line submodel: for the
Gaussian location family at `0` in direction `u`, both equal `‖u‖²`. -/
example (u : E) :
    MathlibExt.Probability.Statistics.FisherInformation.fisherInformation (stdGaussian E)
      (fun t x => pE ((0 : E) + t • u) x) 0 = ‖u‖ ^ 2 := by
  rw [← inner_fisherInformation_self (ν := stdGaussian E) (p := pE) (θ := 0)
    (fun x => Real.exp_pos _) (by unfold pE; fun_prop)
    (fun x => by simpa [pE] using (hasFDerivAt_log_pE 0 x).differentiableAt.exp)
    memLp_score_pE u, fisherInformation_pE,
    ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]

/-- A positive definite operator is invertible. -/
example : IsUnit (ContinuousLinearMap.id ℝ E) :=
  isUnit_of_inner_self_pos fun u hu => by simpa using real_inner_self_pos.2 hu

/-- The first-order Taylor bound is exact for an affine map (`C = 0`). -/
example (A : E →L[ℝ] E) (c θ₀ θ : E) :
    ‖(A θ + c) - (A θ₀ + c) - fderiv ℝ (fun t => A t + c) θ₀ (θ - θ₀)‖ ≤ 0 * ‖θ - θ₀‖ ^ 2 :=
  norm_sub_sub_fderiv_le (f := fun t => A t + c) (δ := ‖θ - θ₀‖ + 1) (fun _ _ => by fun_prop)
    (fun t _ => by simp [(A.hasFDerivAt.add_const c).fderiv])
    (by rw [Metric.mem_ball, dist_eq_norm]; linarith)

/-! ### Boundary: singular information -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- A parameter-free family has zero score. -/
theorem score_const (q : E → ℝ) (θ x : E) : score (fun _ => q) θ x = 0 := by
  simp [score]

omit [BorelSpace E] in
/-- A parameter-free family has zero Fisher information. -/
theorem fisherInformation_const (ν : Measure E) (q : E → ℝ) (θ : E) :
    fisherInformation ν (fun _ => q) θ = 0 := by
  simp [fisherInformation, score_const]

/-- Zero information is singular in positive dimension: the nonsingularity hypothesis of the
matrix Cramér–Rao and asymptotic theorems is not automatic. -/
example [Nontrivial E] (ν : Measure E) (q : E → ℝ) (θ : E) :
    ¬ IsUnit (fisherInformation ν (fun _ => q) θ) := by
  rw [fisherInformation_const]
  exact not_isUnit_zero

end MathlibExtTest.Probability.Statistics.VectorInference
