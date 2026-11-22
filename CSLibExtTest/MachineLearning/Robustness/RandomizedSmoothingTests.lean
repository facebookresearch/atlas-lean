/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Robustness.RandomizedSmoothing

/-!
# Tests for the randomized-smoothing certified radius

* **Linear classifier, exact and tight.** For the half-space classifier
  `z ↦ (⟪z, w⟫ ≤ 0)` with `‖w‖ = 1`, the smoothed probability of `true` at `x` is exactly
  `Φ(-⟪x, w⟫ / σ)`. At a point at distance `m` from the boundary, `p_A = Φ(m / σ)` certifies the
  radius `σ Φ⁻¹(p_A) = m`, the true distance; at `x + m w` both classes have probability `1/2`,
  so no larger radius holds. A `d = 1` threshold instance (`m = 2`, `σ = 1`) instantiates every
  hypothesis.
* **Constant classifier.** The certificates are unbounded: for every `R` some `p_A < 1` certifies a
  radius larger than `R` (the "radius `∞`" case, reached only in the limit `p_A → 1`).
* **Endpoints.** `Φ⁻¹ 1 = 0` and `Φ⁻¹ (1/2) = 0` in the totalized quantile, so `p_A = 1` must be
  excluded rather than read as an infinite radius, and `p_A = 1/2` certifies nothing.
* **Two classes.** With `p_A = Φ 1`, `p_B = Φ (-2)` the two-class radius `3σ/2` exceeds the
  one-class radius `σ`.
* **Noise law.** `smoothedProb` is a probability under Mathlib's `multivariateGaussian x (σ² • 1)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.RandomizedSmoothingTests

open Cslib.MachineLearning.Robustness MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι]

/-- `Φ` takes values in `(0, 1)`. -/
private theorem cdf_gaussianReal_mem_Ioo (y : ℝ) : cdf (gaussianReal 0 1) y ∈ Ioo (0 : ℝ) 1 :=
  ⟨(cdf_nonneg _ (y - 1)).trans_lt (strictMono_cdf_gaussianReal 0 one_ne_zero (sub_one_lt y)),
    (strictMono_cdf_gaussianReal 0 one_ne_zero (lt_add_one y)).trans_le (cdf_le_one _ _)⟩

/-- `Φ⁻¹ ∘ Φ = id`. -/
private theorem cdfQuantile_cdf (y : ℝ) :
    cdfQuantile (gaussianReal 0 1) (cdf (gaussianReal 0 1) y) = y :=
  cdfQuantile_cdf_of_strictMono _ (strictMono_cdf_gaussianReal 0 one_ne_zero) y

/-! ### Linear classifiers: the radius is exact -/

/-- The half-space classifier: `true` on `{⟪z, w⟫ ≤ 0}`. -/
noncomputable def halfSpace (w : EuclideanSpace ℝ ι) (z : EuclideanSpace ℝ ι) : Bool :=
  decide (⟪z, w⟫ ≤ 0)

theorem measurable_halfSpace (w : EuclideanSpace ℝ ι) : Measurable (halfSpace w) := by
  refine measurable_to_bool ?_
  have : halfSpace w ⁻¹' {true} = {z | ⟪z, w⟫ ≤ 0} := by
    ext z
    simp [halfSpace]
  rw [this]
  exact measurableSet_le (by fun_prop) measurable_const

/-- The smoothed probability of `true` for the half-space classifier is `Φ(-⟪x, w⟫ / σ)`. -/
theorem smoothedProb_halfSpace_true {w : EuclideanSpace ℝ ι} (hw : ‖w‖ = 1) {σ : ℝ}
    (hσ : 0 < σ) (x : EuclideanSpace ℝ ι) :
    smoothedProb (halfSpace w) σ x true = cdf (gaussianReal 0 1) (-⟪x, w⟫ / σ) := by
  have hw0 : w ≠ 0 := by
    intro h
    simp [h] at hw
  have hset : {z : EuclideanSpace ℝ ι | halfSpace w (x + σ • z) = true} =
      {z | ⟪z, w⟫ ≤ -⟪x, w⟫ / σ} := by
    ext z
    simp only [halfSpace, decide_eq_true_eq, mem_ofPred_eq, inner_add_left, real_inner_smul_left,
      le_div_iff₀ hσ]
    constructor <;> intro h <;> linarith
  rw [smoothedProb, hset, stdGaussian_real_inner_le hw0, hw, div_one]

/-- The two classes have complementary probabilities. -/
theorem smoothedProb_halfSpace_false (w : EuclideanSpace ℝ ι) (σ : ℝ) (x : EuclideanSpace ℝ ι) :
    smoothedProb (halfSpace w) σ x false = 1 - smoothedProb (halfSpace w) σ x true := by
  have hset : {z : EuclideanSpace ℝ ι | halfSpace w (x + σ • z) = false} =
      {z | halfSpace w (x + σ • z) = true}ᶜ := by
    ext z
    simp
  have hmeas : MeasurableSet {z : EuclideanSpace ℝ ι | halfSpace w (x + σ • z) = true} :=
    (measurable_halfSpace w).comp (by fun_prop) (measurableSet_singleton true)
  rw [smoothedProb, hset, measureReal_compl hmeas, probReal_univ, smoothedProb]

/-- **The certified radius is the distance to the decision boundary.** At a point `x` with
`⟪x, w⟫ = -m`, `m > 0`, the exact probability `p_A = Φ(m / σ)` satisfies the hypotheses of
`smoothedProb_lt_of_norm_lt_quantile`, and its radius `σ Φ⁻¹(p_A)` is `m`. -/
theorem halfSpace_certified {w : EuclideanSpace ℝ ι} (hw : ‖w‖ = 1) {σ m : ℝ} (hσ : 0 < σ)
    {x : EuclideanSpace ℝ ι} (hx : ⟪x, w⟫ = -m) {δ : EuclideanSpace ℝ ι} (hδ : ‖δ‖ < m) :
    smoothedProb (halfSpace w) σ (x + δ) false < smoothedProb (halfSpace w) σ (x + δ) true := by
  have hA : cdf (gaussianReal 0 1) (m / σ) ≤ smoothedProb (halfSpace w) σ x true := by
    rw [smoothedProb_halfSpace_true hw hσ, hx, neg_neg]
  refine smoothedProb_lt_of_norm_lt_quantile (measurable_halfSpace w) hσ
    (cdf_gaussianReal_mem_Ioo _) hA ?_ (by decide)
  rw [cdfQuantile_cdf, mul_div_cancel₀ _ hσ.ne']
  exact hδ

/-- **Tightness.** Moving `x` by `m w` reaches the boundary, where both classes have probability
`1/2`: `true` is no longer strictly most probable at distance `m`, so no radius larger than
`σ Φ⁻¹(p_A) = m` holds for every classifier with `p_A ≤ P(f(x + σZ) = true)`. -/
theorem halfSpace_tight {w : EuclideanSpace ℝ ι} (hw : ‖w‖ = 1) {σ m : ℝ} (hσ : 0 < σ)
    {x : EuclideanSpace ℝ ι} (hx : ⟪x, w⟫ = -m) :
    smoothedProb (halfSpace w) σ (x + m • w) true = 1 / 2 ∧
      smoothedProb (halfSpace w) σ (x + m • w) false = 1 / 2 ∧
      ‖m • w‖ = |m| := by
  have h0 : ⟪x + m • w, w⟫ = 0 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hw, hx]
    ring
  have htrue : smoothedProb (halfSpace w) σ (x + m • w) true = 1 / 2 := by
    rw [smoothedProb_halfSpace_true hw hσ, h0, neg_zero, zero_div, cdf_gaussianReal_zero]
  refine ⟨htrue, ?_, ?_⟩
  · rw [smoothedProb_halfSpace_false, htrue]
    norm_num
  · rw [norm_smul, hw, mul_one, Real.norm_eq_abs]

/-! ### A `d = 1` threshold classifier -/

/-- The unit vector of `ℝ¹`. -/
noncomputable def unitR1 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

theorem norm_unitR1 : ‖unitR1‖ = 1 := by
  rw [unitR1, EuclideanSpace.norm_eq]
  simp

theorem inner_single_unitR1 : ⟪EuclideanSpace.single 0 (-2), unitR1⟫ = -2 := by
  rw [unitR1, EuclideanSpace.inner_single_left]
  simp

/-- `f(z) = (z₀ ≤ 0)` at `x = -2`, `σ = 1`: `p_A = Φ 2` and every `‖δ‖ < 2` is certified. -/
example {δ : EuclideanSpace ℝ (Fin 1)} (hδ : ‖δ‖ < 2) :
    smoothedProb (halfSpace unitR1) 1 (EuclideanSpace.single 0 (-2) + δ) false <
      smoothedProb (halfSpace unitR1) 1 (EuclideanSpace.single 0 (-2) + δ) true :=
  halfSpace_certified norm_unitR1 one_pos inner_single_unitR1 hδ

/-- The same instance: the exact probability is `Φ 2`, and the bound is attained at
`δ = 2 unitR1`. -/
example : smoothedProb (halfSpace unitR1) 1 (EuclideanSpace.single 0 (-2)) true =
      cdf (gaussianReal 0 1) 2 ∧
    smoothedProb (halfSpace unitR1) 1 (EuclideanSpace.single 0 (-2) + (2 : ℝ) • unitR1) true =
      1 / 2 := by
  refine ⟨?_, (halfSpace_tight norm_unitR1 one_pos inner_single_unitR1).1⟩
  rw [smoothedProb_halfSpace_true norm_unitR1 one_pos, inner_single_unitR1]
  norm_num

/-! ### Constant classifiers: unbounded certificates -/

/-- A constant classifier has smoothed probability `1`. -/
theorem smoothedProb_const {Y : Type*} (a : Y) (σ : ℝ) (x : EuclideanSpace ℝ ι) :
    smoothedProb (fun _ => a) σ x a = 1 := by
  simp [smoothedProb]

/-- **Radius `∞` in the limit.** For a constant classifier, every radius `R` is exceeded by the
certificate of some `p_A ∈ (0, 1)`. -/
theorem const_certified_unbounded {Y : Type*} (a : Y) {σ : ℝ} (hσ : 0 < σ)
    (x : EuclideanSpace ℝ ι) (R : ℝ) :
    ∃ pA ∈ Ioo (0 : ℝ) 1, pA ≤ smoothedProb (fun _ => a) σ x a ∧
      R < σ * cdfQuantile (gaussianReal 0 1) pA := by
  refine ⟨cdf (gaussianReal 0 1) (R / σ + 1), cdf_gaussianReal_mem_Ioo _, ?_, ?_⟩
  · rw [smoothedProb_const]
    exact cdf_le_one _ _
  · rw [cdfQuantile_cdf, mul_add, mul_div_cancel₀ _ hσ.ne', mul_one]
    linarith

/-- The unbounded certificates apply: a constant classifier keeps its class at every input. -/
example {σ : ℝ} (hσ : 0 < σ) (x δ : EuclideanSpace ℝ ι) :
    smoothedProb (fun _ => true) σ (x + δ) false < smoothedProb (fun _ => true) σ (x + δ) true := by
  obtain ⟨pA, hpA, hA, hR⟩ := const_certified_unbounded true hσ x ‖δ‖
  exact smoothedProb_lt_of_norm_lt_quantile measurable_const hσ hpA hA hR (by decide)

/-! ### Endpoints of the quantile -/

/-- **Boundary**: the totalized quantile gives `Φ⁻¹ 1 = 0`, not `∞`. Plugging `p_A = 1` into
`σ Φ⁻¹(p_A)` would certify radius `0`; this is why `p_A ∈ (0, 1)` is assumed. -/
example : cdfQuantile (gaussianReal 0 1) 1 = 0 := by
  simp [cdfQuantile]

/-- `Φ⁻¹(1/2) = 0`: `p_A = 1/2` certifies no positive radius. -/
example : cdfQuantile (gaussianReal 0 1) (1 / 2) = 0 := by
  rw [← cdf_gaussianReal_zero, cdfQuantile_cdf]

/-! ### Two classes -/

/-- With `p_A = Φ 1` and `p_B = Φ (-2)` the two-class radius is `3σ/2`, larger than the one-class
radius `σ Φ⁻¹(p_A) = σ`, because `p_B < 1 - p_A`. -/
example (σ : ℝ) (hσ : 0 < σ) :
    σ / 2 * (cdfQuantile (gaussianReal 0 1) (cdf (gaussianReal 0 1) 1) -
        cdfQuantile (gaussianReal 0 1) (cdf (gaussianReal 0 1) (-2))) = 3 / 2 * σ ∧
      σ * cdfQuantile (gaussianReal 0 1) (cdf (gaussianReal 0 1) 1) < 3 / 2 * σ := by
  rw [cdfQuantile_cdf, cdfQuantile_cdf]
  constructor <;> linarith

/-! ### The noise law -/

/-- The smoothed probability is a `N(x, σ² I)` probability of the decision region. -/
example [DecidableEq ι] {w : EuclideanSpace ℝ ι} (σ : ℝ) (x : EuclideanSpace ℝ ι) :
    smoothedProb (halfSpace w) σ x true =
      (multivariateGaussian x (σ ^ 2 • (1 : Matrix ι ι ℝ))).real {z | ⟪z, w⟫ ≤ 0} := by
  rw [smoothedProb_eq_multivariateGaussian (measurable_halfSpace w)]
  congr 1
  ext z
  simp [halfSpace]

end Cslib.MachineLearning.RandomizedSmoothingTests

#print axioms Cslib.MachineLearning.Robustness.smoothedProb_eq_multivariateGaussian
#print axioms Cslib.MachineLearning.Robustness.smoothedProb_lower
#print axioms Cslib.MachineLearning.Robustness.smoothedProb_upper
#print axioms Cslib.MachineLearning.Robustness.smoothedProb_lt_of_norm_lt
#print axioms Cslib.MachineLearning.Robustness.smoothedProb_lt_of_norm_lt_quantile
#print axioms Cslib.MachineLearning.RandomizedSmoothingTests.halfSpace_certified
#print axioms Cslib.MachineLearning.RandomizedSmoothingTests.halfSpace_tight
#print axioms Cslib.MachineLearning.RandomizedSmoothingTests.const_certified_unbounded
