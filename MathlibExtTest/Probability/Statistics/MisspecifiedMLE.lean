/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MisspecifiedMLE

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
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped RealInnerProductSpace ENNReal

namespace MathlibExtTest.Probability.Statistics.MisspecifiedMLE

open MathlibExt.Probability.Statistics.MLEConsistency
open MathlibExt.Probability.Statistics.MisspecifiedMLE

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

theorem hasGradientAt_ell (b : Bool) (θ : ℝ) :
    HasGradientAt (fun t => ell t b) (psi θ b) θ := by
  have h1 : HasDerivAt (fun t => val b - t) (-1) θ := (hasDerivAt_id' θ).const_sub (val b)
  have h2 := (h1.mul h1).neg.div_const 2
  have e1 : (fun t => ell t b) = fun y => -((val b - y) * (val b - y)) / 2 := by
    funext t
    simp only [ell]
    ring
  have e2 : psi θ b = -(-1 * (val b - θ) + (val b - θ) * -1) / 2 := by
    simp only [psi]
    ring
  rw [e1, e2]
  exact HasDerivAt.hasGradientAt' h2

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

/-- **The sandwich variance is `4`**: the variance of the limit law in
`tendstoInDistribution_sqrt_smul_sub_of_isMLEOn` for the misspecified model. -/
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

end MathlibExtTest.Probability.Statistics.MisspecifiedMLE
