/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MisspecifiedMLE
public import MathlibExtTest.Probability.Statistics.MLEConsistency
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure

/-!
# Tests for the misspecified maximum-likelihood estimator

The working model is the unit-variance Gaussian location model, with log-likelihood
`ell θ x = -(x - θ)² / 2` (up to a constant) and score `psi θ x = x - θ`. The true law is the
two-point law putting mass `1/2` on `0` and on `4` (realized on `Bool` through `val`), which has
mean `2` and variance `4` and is not a unit-variance Gaussian. Every integral is computed from
the definitions (`integral_trueLaw`), not through the theorems under test.

* **Interior pseudo-true value (non-vacuity).** The expected log-likelihood is
  `-((4 - θ)² + θ²) / 4`, maximized at `θ* = 2`; `integral_eq_zero_of_isLocalMax` applies there
  and its conclusion `E psi 2 = 0` agrees with the direct computation.
* **Boundary pseudo-true value.** On `K = [0, 1]` the maximizer of the expected log-likelihood is
  the boundary point `1`, where the expected score is `1 ≠ 0`: the first-order condition needs an
  interior (local) maximum.
* **Roots of the likelihood equation.** For the constant sample `4, 4, …`, the MLE on `[0, 8]` is
  the interior point `4` and `sum_eq_zero_of_isMLEOn` applies; on `[0, 1]` the MLE is the boundary
  point `1` and `∑_{i<n} psi 1 (X i) = 3 n ≠ 0` for `n ≥ 1`, so the neighbourhood hypothesis is
  needed.
* **Sandwich versus inverse information.** At `θ* = 2`, `A = E D psi = -1` and the meat
  `B = covarianceOperator` of the law of `psi 2` has quadratic form `4`. The sandwich variance in
  the conclusion of `tendstoInDistribution_sqrt_smul_sub_of_isMLEOn` is `4`, while the inverse of
  the model information `-A = 1` is `1`: under misspecification the sandwich does not collapse to
  the inverse information.
* **Kullback–Leibler projection.** The true law `Ber(3/4)` is fitted by the Bernoulli model
  `Ber(θ)`, `θ ∈ K = [1/4, 1/2]`, which does not contain it. `KL(Ber(3/4) ‖ Ber(θ))` is computed
  from `klDiv` (`toReal_klDiv_bern`), its unique minimizer on `K` is the boundary point `1/2`
  (`isKLProjectionOn_bern`), and every hypothesis of
  `isIdentifiedOn_popCrit_iff_isKLProjectionOn_of_density` holds for IID coordinates on the
  product space `Measure.infinitePi`, so `1/2` is the pseudo-true value.
* **Consistency for the KL projection (non-degenerate).** For the same IID sample, every
  hypothesis of `ae_tendsto_of_isMLEOn_of_isKLProjectionOn` holds, the uniform LLN derived from
  the strong law (the Bernoulli log-likelihood has rank 2), so every MLE on `K` converges almost
  surely to `1/2`; an MLE exists.
* **White's theorem end to end (degenerate).** For the IID sample with law `dirac 4` (so the
  sample is almost surely constant, as in the non-vacuity test of `MLEConsistency`), the
  Gaussian location model on `K = [0, 8]`, the clamped sample mean as MLE, `θ* = 4`, `M = 0`, the
  meat is `0` and the limit is `Z = 0`: every hypothesis of
  `tendstoInDistribution_sqrt_smul_sub_of_isMLEOn` holds at once. The instance is degenerate; a
  non-degenerate end-to-end instance is not constructed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Metric Set
open scoped RealInnerProductSpace ENNReal

namespace MathlibExtTest.Probability.Statistics.MisspecifiedMLE

open MathlibExt.Probability.Statistics.MLEConsistency
open MathlibExt.Probability.Statistics.MisspecifiedMLE
open MathlibExt.Probability.Statistics.InformationInequalityIdentification

/-! ## The two-point true law and the Gaussian location model -/

/-- The observation value: `4` on `true`, `0` on `false`. -/
def val (b : Bool) : ℝ := if b then 4 else 0

/-- The true law: mass `1/2` on each point of `Bool`, so `val` is `0` or `4` with probability
`1/2`. -/
noncomputable def trueLaw : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsFiniteMeasure trueLaw :=
  ⟨by
    rw [trueLaw, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)⟩

/-- The unit-variance Gaussian location log-likelihood, up to an additive constant. -/
noncomputable def ell (θ : ℝ) (b : Bool) : ℝ := -(val b - θ) ^ 2 / 2

/-- The score of `ell`. -/
noncomputable def psi (θ : ℝ) (b : Bool) : ℝ := val b - θ

theorem integral_trueLaw (f : Bool → ℝ) : ∫ b, f b ∂trueLaw = (f true + f false) / 2 := by
  rw [integral_fintype Integrable.of_finite]
  simp [trueLaw, measureReal_def]
  ring

theorem integral_ell (θ : ℝ) : ∫ b, ell θ b ∂trueLaw = -((4 - θ) ^ 2 + θ ^ 2) / 4 := by
  rw [integral_trueLaw]
  simp only [ell, val, ite_true, Bool.false_eq_true, ite_false]
  ring

theorem integral_psi (θ : ℝ) : ∫ b, psi θ b ∂trueLaw = 2 - θ := by
  rw [integral_trueLaw]
  simp only [psi, val, ite_true, Bool.false_eq_true, ite_false]
  ring

theorem hasGradientAt_gaussLL (x θ : ℝ) :
    HasGradientAt (fun t => MLEConsistency.gaussLL t x) (x - θ) θ := by
  have h1 : HasDerivAt (fun t => x - t) (-1) θ := (hasDerivAt_id' θ).const_sub x
  have h2 := (h1.mul h1).neg.div_const 2
  have e1 : (fun t => MLEConsistency.gaussLL t x) = fun y => -((x - y) * (x - y)) / 2 := by
    funext t
    simp only [MLEConsistency.gaussLL]
    ring
  have e2 : x - θ = -(-1 * (x - θ) + (x - θ) * -1) / 2 := by ring
  rw [e1, e2]
  exact HasDerivAt.hasGradientAt' h2

theorem hasGradientAt_ell (b : Bool) (θ : ℝ) :
    HasGradientAt (fun t => ell t b) (psi θ b) θ :=
  hasGradientAt_gaussLL (val b) θ

/-! ## Interior pseudo-true value -/

/-- The expected log-likelihood is maximized at `2`: computed from the definitions. -/
theorem isLocalMax_integral_ell : IsLocalMax (fun θ => ∫ b, ell θ b ∂trueLaw) 2 :=
  Filter.Eventually.of_forall fun θ => by
    simp only [integral_ell]
    nlinarith [sq_nonneg (θ - 2)]

theorem norm_psi_le (b : Bool) {θ : ℝ} (hθ : θ ∈ ball (2 : ℝ) 1) : ‖psi θ b‖ ≤ 10 := by
  rw [mem_ball, Real.dist_eq, abs_lt] at hθ
  rw [Real.norm_eq_abs, abs_le]
  cases b <;> simp only [psi, val, ite_true, Bool.false_eq_true, ite_false] <;>
    constructor <;> linarith

/-- **Non-vacuity of the first-order condition**: every hypothesis of
`integral_eq_zero_of_isLocalMax` holds at the interior pseudo-true value `2`. -/
theorem integral_psi_two_eq_zero : ∫ b, psi 2 b ∂trueLaw = 0 :=
  integral_eq_zero_of_isLocalMax one_pos isLocalMax_integral_ell
    (fun b θ _ => hasGradientAt_ell b θ) (fun _ _ => Integrable.of_finite.aestronglyMeasurable)
    Integrable.of_finite Integrable.of_finite.aestronglyMeasurable
    (G := fun _ => 10) Integrable.of_finite fun b _ hθ => norm_psi_le b hθ

/-- The conclusion agrees with the direct computation. -/
example : ∫ b, psi 2 b ∂trueLaw = 0 := by
  rw [integral_psi]
  norm_num

/-! ## Boundary pseudo-true value -/

/-- On `K = [0, 1]` the expected log-likelihood is maximized at the boundary point `1`. -/
theorem isMaxOn_integral_ell_one : IsMaxOn (fun θ => ∫ b, ell θ b ∂trueLaw) (Icc 0 1) 1 :=
  fun θ hθ => by
    simp only [mem_ofPred_eq, integral_ell]
    nlinarith [hθ.1, hθ.2]

/-- **At the boundary maximizer the expected score does not vanish**: the first-order condition
`integral_eq_zero_of_isLocalMax` needs an interior maximum. -/
theorem integral_psi_one_ne_zero : ∫ b, psi 1 b ∂trueLaw ≠ 0 := by
  rw [integral_psi]
  norm_num

/-! ## Roots of the likelihood equation -/

/-- The constant sample `4, 4, …`. -/
def sample (_ : ℕ) (_ : Unit) : Bool := true

theorem avgLogLik_sample (n : ℕ) (u : Unit) (θ : ℝ) :
    avgLogLik ell sample n u θ = (n : ℝ)⁻¹ * (n * ell θ true) := by
  simp [avgLogLik, sample]

theorem isMLEOn_sample {K : Set ℝ} {c : ℝ} (hc : c ∈ K)
    (hmax : ∀ θ ∈ K, ell θ true ≤ ell c true) :
    IsMLEOn K ell sample fun _ _ => c := fun n _ =>
  ⟨hc, fun θ hθ => by
    rw [avgLogLik_sample, avgLogLik_sample]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hmax θ hθ) (Nat.cast_nonneg n))
      (inv_nonneg.2 (Nat.cast_nonneg n))⟩

/-- On `[0, 8]` the MLE for the constant sample is the interior point `4`. -/
theorem isMLEOn_sample_four : IsMLEOn (Icc 0 8) ell sample fun _ _ => 4 :=
  isMLEOn_sample ⟨by norm_num, by norm_num⟩ fun θ _ => by
    simp only [ell, val, ite_true]
    nlinarith [sq_nonneg (4 - θ)]

/-- **Non-vacuity of `sum_eq_zero_of_isMLEOn`** at an interior MLE. -/
example (n : ℕ) : ∑ i ∈ Finset.range n, psi 4 (sample i ()) = 0 :=
  sum_eq_zero_of_isMLEOn isMLEOn_sample_four (Icc_mem_nhds (by norm_num) (by norm_num))
    fun i _ => hasGradientAt_ell _ _

/-- On `[0, 1]` the MLE for the constant sample is the boundary point `1`. -/
theorem isMLEOn_sample_one : IsMLEOn (Icc 0 1) ell sample fun _ _ => 1 :=
  isMLEOn_sample ⟨by norm_num, by norm_num⟩ fun θ hθ => by
    simp only [ell, val, ite_true]
    nlinarith [hθ.1, hθ.2]

/-- **At a boundary MLE the likelihood equation fails**: the score sum is `3 n ≠ 0`. -/
theorem sum_psi_one_ne_zero {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, psi 1 (sample i ()) ≠ 0 := by
  simp only [psi, sample, val, ite_true, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (0 : ℝ) < n := Nat.cast_pos.2 hn
  nlinarith

/-! ## Sandwich versus inverse information -/

theorem fderiv_psi (b : Bool) (θ : ℝ) :
    fderiv ℝ (fun t => psi t b) θ = -ContinuousLinearMap.id ℝ ℝ :=
  ((hasFDerivAt_id θ).const_sub (val b)).fderiv

/-- The bread `A = E D psi 2 = -1`. -/
theorem trueLaw_real_univ : trueLaw.real univ = 1 := by
  have h := integral_trueLaw fun _ => (1 : ℝ)
  rw [integral_const, smul_eq_mul, mul_one] at h
  rw [h]
  norm_num

theorem bread_eq : ∫ b, fderiv ℝ (fun t => psi t b) 2 ∂trueLaw = -1 := by
  simp only [fderiv_psi, integral_const, trueLaw_real_univ, one_smul]
  rw [ContinuousLinearMap.one_def]

/-- The meat: `⟪B 1, 1⟫ = E (psi 2)² = 4`. -/
theorem inner_meat_one :
    ⟪covarianceOperator (trueLaw.map (psi 2)) 1, 1⟫ = 4 := by
  have hm : Measurable (psi 2) := measurable_of_finite _
  have hμ : MemLp id 2 (trueLaw.map (psi 2)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable).2 MemLp.of_discrete
  rw [covarianceOperator_inner hμ, integral_map hm.aemeasurable
    (by fun_prop : Continuous fun z : ℝ => ⟪(1 : ℝ), z⟫ * ⟪(1 : ℝ), z⟫).aestronglyMeasurable,
    integral_trueLaw]
  simp only [psi, val, ite_true, Bool.false_eq_true, ite_false, RCLike.inner_apply, conj_trivial]
  norm_num

theorem ring_inverse_neg_one : Ring.inverse (-1 : ℝ →L[ℝ] ℝ) = -1 :=
  Ring.inverse_unit (-1 : (ℝ →L[ℝ] ℝ)ˣ)

/-- **The sandwich variance is `4`**: the variance expression in the conclusion of
`tendstoInDistribution_sqrt_smul_sub_of_isMLEOn`, evaluated for the misspecified model. -/
theorem sandwich_eq_four :
    ⟪ProbabilityTheory.GEE.sandwichCovariance
        (∫ b, fderiv ℝ (fun t => psi t b) 2 ∂trueLaw)
        (covarianceOperator (trueLaw.map (psi 2))) 1, 1⟫ = 4 := by
  rw [ProbabilityTheory.GEE.inner_sandwichCovariance_apply, bread_eq, ring_inverse_neg_one,
    map_neg, ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]
  simp only [_root_.neg_apply, ContinuousLinearMap.id_apply, map_neg,
    inner_neg_neg]
  exact inner_meat_one

/-- **The inverse model information is `1`**: the model information at `2` is `-A = 1`. -/
theorem inverse_information_eq_one :
    ⟪Ring.inverse (-∫ b, fderiv ℝ (fun t => psi t b) 2 ∂trueLaw) 1, 1⟫ = 1 := by
  rw [bread_eq, neg_neg, Ring.inverse_one]
  simp

/-- Under misspecification the sandwich does not reduce to the inverse information. -/
example :
    ⟪ProbabilityTheory.GEE.sandwichCovariance
        (∫ b, fderiv ℝ (fun t => psi t b) 2 ∂trueLaw)
        (covarianceOperator (trueLaw.map (psi 2))) 1, 1⟫ ≠
      ⟪Ring.inverse (-∫ b, fderiv ℝ (fun t => psi t b) 2 ∂trueLaw) 1, 1⟫ := by
  rw [sandwich_eq_four, inverse_information_eq_one]
  norm_num

/-! ## IID coordinates on the product space -/

section IID

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

theorem hasLaw_eval (i : ℕ) :
    HasLaw (fun ω : ℕ → α => ω i) μ (Measure.infinitePi fun _ => μ) :=
  ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

theorem iIndepFun_eval :
    iIndepFun (fun i (ω : ℕ → α) => ω i) (Measure.infinitePi fun _ => μ) :=
  iIndepFun_infinitePi (P := fun _ => μ) (X := fun _ => id) fun _ => measurable_id

theorem identDistrib_eval (i : ℕ) :
    IdentDistrib (fun ω : ℕ → α => ω i) (fun ω => ω 0) (Measure.infinitePi fun _ => μ)
      (Measure.infinitePi fun _ => μ) :=
  ⟨(hasLaw_eval μ i).aemeasurable, (hasLaw_eval μ 0).aemeasurable,
    (hasLaw_eval μ i).map_eq.trans (hasLaw_eval μ 0).map_eq.symm⟩

theorem integrable_comp_eval {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun ω : ℕ → α => f (ω 0)) (Measure.infinitePi fun _ => μ) :=
  (integrable_map_measure (by rw [(hasLaw_eval μ 0).map_eq]; exact hf.aestronglyMeasurable)
    (hasLaw_eval μ 0).aemeasurable).1 (by rw [(hasLaw_eval μ 0).map_eq]; exact hf)

end IID

/-! ## The Kullback–Leibler projection of `Ber(3/4)` onto `Ber(θ)`, `θ ∈ [1/4, 1/2]` -/

/-- The Bernoulli density with success probability `q` with respect to the counting measure on
`Bool`. -/
noncomputable def bernDens (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

theorem bernDens_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) : 0 ≤ bernDens q b := by
  cases b <;> simp [bernDens] <;> linarith

theorem bernDens_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (b : Bool) : 0 < bernDens q b := by
  cases b <;> simp [bernDens] <;> linarith

theorem isProbabilityMeasure_bern {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsProbabilityMeasure (densityModel Measure.count bernDens q) := by
  constructor
  rw [densityModel, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
    tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun b _ => bernDens_nonneg hq0 hq1 b]
  simp [bernDens]

/-- Integrals against a Bernoulli law, computed from the definitions. -/
theorem integral_bern {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂densityModel Measure.count bernDens q = q * f true + (1 - q) * f false := by
  rw [densityModel, integral_withDensity_eq_integral_toReal_smul (measurable_of_countable _)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), integral_count, Fintype.sum_bool]
  simp [bernDens, ENNReal.toReal_ofReal hq0, ENNReal.toReal_ofReal (sub_nonneg.2 hq1)]

/-- The true law `Ber(3/4)` is a probability measure. -/
instance : IsProbabilityMeasure (densityModel Measure.count bernDens (3 / 4)) :=
  isProbabilityMeasure_bern (by norm_num) (by norm_num)

theorem absolutelyContinuous_bern {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    densityModel Measure.count bernDens (3 / 4) ≪ densityModel Measure.count bernDens θ :=
  densityModel_absolutelyContinuous (measurable_of_countable _)
    (ae_of_all _ fun b => bernDens_pos h0 h1 b)

theorem klDiv_bern_ne_top {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    klDiv (densityModel Measure.count bernDens (3 / 4)) (densityModel Measure.count bernDens θ)
      ≠ ∞ :=
  klDiv_ne_top (absolutelyContinuous_bern h0 h1) Integrable.of_finite

/-- `KL(Ber(3/4) ‖ Ber(θ))`, computed from `klDiv` and the log-likelihood ratio of the
densities. -/
theorem toReal_klDiv_bern {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    (klDiv (densityModel Measure.count bernDens (3 / 4))
      (densityModel Measure.count bernDens θ)).toReal =
      3 / 4 * Real.log (3 / 4) + 1 / 4 * Real.log (1 / 4) -
        (3 / 4 * Real.log θ + 1 / 4 * Real.log (1 - θ)) := by
  have := isProbabilityMeasure_bern h0.le h1.le
  rw [toReal_klDiv_of_measure_eq (absolutelyContinuous_bern h0 h1)
      (by rw [measure_univ, measure_univ]),
    ← integral_congr_ae (llr_densityModel_ae_eq (ν := Measure.count) (p := bernDens)
      (θ₀ := 3 / 4) (θ := θ) (measurable_of_countable _) (measurable_of_countable _)
      (ae_of_all _ (bernDens_pos (by norm_num) (by norm_num))) (ae_of_all _ (bernDens_pos h0 h1))),
    integral_bern (by norm_num) (by norm_num)]
  simp only [logDensity, bernDens, ite_true, Bool.false_eq_true, ite_false]
  rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num]
  ring

/-- **The KL projection of `Ber(3/4)` onto `{Ber(θ) : θ ∈ [1/4, 1/2]}` is the boundary point
`1/2`**, from the computed divergence: `θ³ (1 - θ)` increases on `[1/4, 1/2]`. -/
theorem isKLProjectionOn_bern :
    IsKLProjectionOn (Icc (1 / 4 : ℝ) (1 / 2)) (densityModel Measure.count bernDens (3 / 4))
      (densityModel Measure.count bernDens) (1 / 2) := by
  refine ⟨by norm_num [mem_Icc], fun θ hθ hne => ?_⟩
  have h0 : 0 < θ := by linarith [hθ.1]
  have h1 : θ < 1 := by linarith [hθ.2]
  have hlt : θ < 1 / 2 := lt_of_le_of_ne hθ.2 hne
  rw [← ENNReal.toReal_lt_toReal (klDiv_bern_ne_top (by norm_num) (by norm_num))
      (klDiv_bern_ne_top h0 h1), toReal_klDiv_bern (by norm_num) (by norm_num),
    toReal_klDiv_bern h0 h1]
  have hf : 0 < -θ ^ 3 + θ ^ 2 / 2 + θ / 4 + 1 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_right hθ.2 (sq_nonneg θ)]
  have key : θ ^ 3 * (1 - θ) < (1 / 2) ^ 4 := by nlinarith [mul_pos (sub_pos.2 hlt) hf]
  have hpos : 0 < θ ^ 3 * (1 - θ) := mul_pos (pow_pos h0 3) (sub_pos.2 h1)
  have hlog := Real.log_lt_log hpos key
  rw [Real.log_mul (pow_pos h0 3).ne' (sub_pos.2 h1).ne', Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  linarith

/-- The IID sample with law `Ber(3/4)`: the coordinates of the product space. -/
noncomputable def bernP : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ => densityModel Measure.count bernDens (3 / 4)

instance : IsProbabilityMeasure bernP := by
  unfold bernP
  infer_instance

theorem prob_bern_K {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2)) :
    IsProbabilityMeasure (densityModel Measure.count bernDens θ) :=
  isProbabilityMeasure_bern (by linarith [hθ.1]) (by linarith [hθ.2])

theorem pos_bern_K {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2)) :
    ∀ᵐ b ∂Measure.count, 0 < bernDens θ b :=
  ae_of_all _ (bernDens_pos (by linarith [hθ.1]) (by linarith [hθ.2]))

/-- **Non-vacuity of `isIdentifiedOn_popCrit_iff_isKLProjectionOn_of_density`**: every hypothesis
holds for the IID `Ber(3/4)` sample, and the KL projection `1/2` is the pseudo-true value. -/
theorem isIdentifiedOn_bern :
    IsIdentifiedOn (Icc (1 / 4 : ℝ) (1 / 2))
      (popCrit bernP (logDensity bernDens) fun i ω => ω i) (1 / 2) := by
  have : IsProbabilityMeasure
      (Measure.count.withDensity fun x => ENNReal.ofReal (bernDens (3 / 4) x)) :=
    isProbabilityMeasure_bern (by norm_num) (by norm_num)
  exact (isIdentifiedOn_popCrit_iff_isKLProjectionOn_of_density (g := bernDens (3 / 4))
    (measurable_of_countable _) (ae_of_all _ (bernDens_pos (by norm_num) (by norm_num)))
    (fun θ hθ => prob_bern_K hθ) (fun _ _ => measurable_of_countable _)
    (fun θ hθ => pos_bern_K hθ) (hasLaw_eval _ 0).aemeasurable (hasLaw_eval _ 0).map_eq
    Integrable.of_finite (fun _ _ => Integrable.of_finite)).2 isKLProjectionOn_bern

/-- The expected log-likelihood of the Bernoulli model under `Ber(3/4)`, from the definitions. -/
theorem popCrit_bern (θ : ℝ) :
    popCrit bernP (logDensity bernDens) (fun i ω => ω i) θ =
      3 / 4 * Real.log θ + 1 / 4 * Real.log (1 - θ) := by
  have h := (hasLaw_eval (densityModel Measure.count bernDens (3 / 4)) 0).integral_comp
    (f := logDensity bernDens θ) Integrable.of_finite.aestronglyMeasurable
  rw [integral_bern (by norm_num) (by norm_num)] at h
  unfold popCrit
  refine h.trans ?_
  simp only [logDensity, bernDens, ite_true, Bool.false_eq_true, ite_false]
  rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num]

/-- Independent check of the identification at `θ = 1/4`, from the definitions:
`3/4 log (1/4) + 1/4 log (3/4) < log (1/2)`. -/
example :
    popCrit bernP (logDensity bernDens) (fun i ω => ω i) (1 / 4) <
      popCrit bernP (logDensity bernDens) (fun i ω => ω i) (1 / 2) := by
  rw [popCrit_bern, popCrit_bern]
  have h : Real.log ((1 / 4) ^ 3 * (3 / 4)) < Real.log ((1 / 2) ^ 4) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow] at h
  push_cast at h
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  linarith

/-! ## Consistency for the KL projection -/

/-- Coefficients of the rank-2 decomposition of the Bernoulli log-likelihood. -/
noncomputable def bernA : Fin 2 → ℝ → ℝ := ![fun θ => Real.log θ, fun θ => Real.log (1 - θ)]

/-- Statistics of the rank-2 decomposition of the Bernoulli log-likelihood. -/
noncomputable def bernG : Fin 2 → Bool → ℝ :=
  ![fun b => if b then 1 else 0, fun b => if b then 0 else 1]

theorem logDensity_bern_eq (θ : ℝ) (b : Bool) :
    logDensity bernDens θ b = ∑ j, bernA j θ * bernG j b := by
  cases b <;> simp [logDensity, bernDens, bernA, bernG, Fin.sum_univ_two]

theorem continuousOn_bernA (j : Fin 2) : ContinuousOn (bernA j) (Icc (1 / 4 : ℝ) (1 / 2)) := by
  fin_cases j
  · show ContinuousOn (fun θ : ℝ => Real.log θ) _
    exact continuousOn_id.log fun θ hθ => (by linarith [hθ.1] : (0 : ℝ) < θ).ne'
  · show ContinuousOn (fun θ : ℝ => Real.log (1 - θ)) _
    exact (continuousOn_const.sub continuousOn_id).log fun θ hθ =>
      (by linarith [hθ.2] : (0 : ℝ) < 1 - θ).ne'

theorem continuousOn_logDensity_bern (b : Bool) :
    ContinuousOn (fun θ => logDensity bernDens θ b) (Icc (1 / 4 : ℝ) (1 / 2)) := by
  simp_rw [logDensity_bern_eq]
  exact continuousOn_finsetSum _ fun j _ => (continuousOn_bernA j).mul continuousOn_const

/-- The uniform LLN for the Bernoulli log-likelihood on `[1/4, 1/2]`, from the strong law. -/
theorem uniformLLNOn_bern :
    UniformLLNOn bernP (Icc (1 / 4 : ℝ) (1 / 2)) (logDensity bernDens) fun i ω => ω i :=
  uniformLLNOn_of_finiteRank_of_continuousOn isCompact_Icc bernA bernG logDensity_bern_eq
    continuousOn_bernA (fun _ => measurable_of_countable _)
    (fun _ => integrable_comp_eval _ Integrable.of_finite)
    (fun _ _ hij => (iIndepFun_eval _).indepFun hij) (identDistrib_eval _)

/-- **Non-vacuity of `ae_tendsto_of_isMLEOn_of_isKLProjectionOn`**: for the IID `Ber(3/4)`
sample, every MLE of the Bernoulli model on `[1/4, 1/2]` converges almost surely to the KL
projection `1/2`. -/
theorem ae_tendsto_bern {est : ℕ → (ℕ → Bool) → ℝ}
    (hest : IsMLEOn (Icc (1 / 4 : ℝ) (1 / 2)) (logDensity bernDens) (fun i ω => ω i) est) :
    ∀ᵐ ω ∂bernP, Tendsto (fun n => est n ω) atTop (𝓝 (1 / 2)) := by
  have : IsProbabilityMeasure
      (Measure.count.withDensity fun x => ENNReal.ofReal (bernDens (3 / 4) x)) :=
    isProbabilityMeasure_bern (by norm_num) (by norm_num)
  exact ae_tendsto_of_isMLEOn_of_isKLProjectionOn (g := bernDens (3 / 4)) isCompact_Icc
    (measurable_of_countable _) (ae_of_all _ (bernDens_pos (by norm_num) (by norm_num)))
    (fun θ hθ => prob_bern_K hθ) (fun _ _ => measurable_of_countable _)
    (fun θ hθ => pos_bern_K hθ) (hasLaw_eval _ 0).aemeasurable (hasLaw_eval _ 0).map_eq
    Integrable.of_finite (fun _ _ => Integrable.of_finite) isKLProjectionOn_bern
    continuousOn_logDensity_bern uniformLLNOn_bern hest

/-- An MLE of the Bernoulli model on `[1/4, 1/2]` exists, so `ae_tendsto_bern` is not vacuous. -/
example : ∃ est : ℕ → (ℕ → Bool) → ℝ,
    IsMLEOn (Icc (1 / 4 : ℝ) (1 / 2)) (logDensity bernDens) (fun i ω => ω i) est :=
  exists_isMLEOn isCompact_Icc ⟨1 / 2, by norm_num [mem_Icc]⟩ continuousOn_logDensity_bern _

/-! ## White's theorem end to end: a degenerate instance -/

/-- The IID sample with law `dirac 4`: the coordinates of the product space. -/
noncomputable def diracP : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => Measure.dirac (4 : ℝ)

instance : IsProbabilityMeasure diracP := by
  unfold diracP
  infer_instance

theorem integral_comp_eval_dirac {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ ω, f (ω 0) ∂diracP = f 4 := by
  rw [← integral_dirac f 4]
  exact (hasLaw_eval (Measure.dirac (4 : ℝ)) 0).integral_comp hf.aestronglyMeasurable

theorem fderiv_const_sub_id (x θ : ℝ) :
    fderiv ℝ (fun t => x - t) θ = -ContinuousLinearMap.id ℝ ℝ :=
  ((hasFDerivAt_id θ).const_sub x).fderiv

theorem continuous_gaussLL_left (θ : ℝ) : Continuous (MLEConsistency.gaussLL θ) := by
  show Continuous fun x : ℝ => -(x - θ) ^ 2 / 2
  fun_prop

/-- **Every hypothesis of `tendstoInDistribution_sqrt_smul_sub_of_isMLEOn` holds at once** for
the IID `dirac 4` sample, the Gaussian location model on `[0, 8]` and the clamped sample mean, with
`θ* = 4`, `ψ θ x = x - θ`, `M = 0`: the meat is `0` and the limit is `Z = 0`. The instance is
degenerate (the sample is almost surely constant). -/
theorem tendstoInDistribution_dirac :
    TendstoInDistribution
      (fun (n : ℕ) ω => √n • (MLEConsistency.clampMLE 0 8 (fun i (ω : ℕ → ℝ) => ω i) n ω - 4))
      atTop (fun _ : Unit => (0 : ℝ)) (fun _ => diracP) (Measure.dirac ()) := by
  have hX_law : ∀ i, HasLaw (fun ω : ℕ → ℝ => ω i) (Measure.dirac (4 : ℝ)) diracP :=
    hasLaw_eval _
  have hX_indep : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) diracP := iIndepFun_eval _
  have hint1 : Integrable (fun ω : ℕ → ℝ => ω 0) diracP :=
    integrable_comp_eval _ (f := id) (integrable_dirac enorm_lt_top)
  have hint2 : Integrable (fun ω : ℕ → ℝ => ω 0 ^ 2) diracP :=
    integrable_comp_eval _ (f := fun x => x ^ 2) (integrable_dirac enorm_lt_top)
  have hindep : Pairwise fun i j => (fun ω : ℕ → ℝ => ω i) ⟂ᵢ[diracP] fun ω => ω j :=
    fun _ _ hij => hX_indep.indepFun hij
  have hmean : ∫ ω, ω 0 ∂diracP = 4 := integral_comp_eval_dirac continuous_id
  have hId : IsIdentifiedOn (Icc 0 8)
      (popCrit diracP MLEConsistency.gaussLL fun i ω => ω i) 4 := by
    have h := MLEConsistency.gauss_isIdentifiedOn (X := fun i (ω : ℕ → ℝ) => ω i) (a := 0)
      (b := 8) hint1 hint2 (by rw [hmean]; norm_num [mem_Icc])
    rwa [hmean] at h
  have hA : IsUnit (∫ x, fderiv ℝ (fun t => x - t) 4 ∂Measure.dirac (4 : ℝ)) := by
    simp only [fderiv_const_sub_id, integral_const, probReal_univ, one_smul]
    rw [← ContinuousLinearMap.one_def]
    exact isUnit_one.neg
  refine tendstoInDistribution_sqrt_smul_sub_of_isMLEOn (ψ := fun θ x => x - θ) (δ := 1)
    (G := fun x => |x| + 5) (M := fun _ => 0) hX_law hX_indep isCompact_Icc
    (fun x => (MLEConsistency.continuous_gaussLL x).continuousOn)
    (MLEConsistency.gauss_uniformLLNOn 0 8 hint1 hint2 hindep (identDistrib_eval _)) hId
    (by rw [interior_Icc]; constructor <;> norm_num)
    (MLEConsistency.isMLEOn_clampMLE (by norm_num) _) (fun n => ?_) one_pos
    (fun x θ _ => hasGradientAt_gaussLL x θ)
    (fun θ _ => (continuous_gaussLL_left θ).aestronglyMeasurable)
    (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top) (fun x θ hθ => ?_)
    (fun x θ _ => ((hasFDerivAt_id θ).const_sub x).differentiableAt) measurable_const
    (integrable_dirac enorm_lt_top) (fun x θ _ => by simp [fderiv_const_sub_id])
    (measurable_id.sub_const 4) (integrable_dirac enorm_lt_top)
    (by simp only [fderiv_const_sub_id]; exact stronglyMeasurable_const)
    (integrable_dirac enorm_lt_top) hA aemeasurable_const (fun t => ?_)
  · show AEStronglyMeasurable
      (fun ω : ℕ → ℝ => max 0 (min 8 ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ω i))) diracP
    exact (measurable_const.max (measurable_const.min (measurable_const.mul
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)))).aestronglyMeasurable
  · rw [mem_ball, Real.dist_eq, abs_lt] at hθ
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [le_abs_self x, neg_abs_le x]
  · have hB : ∀ v : ℝ,
        ⟪covarianceOperator ((Measure.dirac (4 : ℝ)).map fun x => x - 4) v, v⟫ = 0 := fun v => by
      rw [Measure.map_dirac' (f := fun x : ℝ => x - 4) (by fun_prop),
        covarianceOperator_inner (memLp_dirac enorm_lt_top), integral_dirac]
      simp
    rw [ProbabilityTheory.GEE.inner_sandwichCovariance_apply, hB, Real.toNNReal_zero,
      gaussianReal_zero_var]
    exact ⟨aemeasurable_const, by simp⟩

end MathlibExtTest.Probability.Statistics.MisspecifiedMLE
