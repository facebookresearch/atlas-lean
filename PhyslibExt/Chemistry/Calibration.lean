/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.Statistics.GaussMarkov
public import MathlibExt.Probability.Statistics.LinearModel.Sampling
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import PhyslibExt.Chemistry.Uncertainty.Propagation

/-!
# Analytical calibration: regression, figures of merit and inverse prediction

Gauss-Markov unbiasedness and BLUE for calibration lines, first-order inverse-prediction
uncertainty, standard addition and internal standards.

## i. Overview

Calibration data are finitely many pairs `(x i, y i)`, where `x i` is the known concentration of
standard `i` and `y i` is the measured response. That `x` is error-free is a MODEL hypothesis,
stated explicitly where it is used. The calibration line is an empirical fit with no truth claim:
no statement below asserts that the true response is linear, and the line carries no validity
outside the calibrated range (extrapolation gets no theorem). A near-`1` `R²` proves nothing about
linearity; `R²` is not defined or used here. Concentrations and responses are real numbers after a
consistent choice of units, the convention of `Chemistry.Amounts`, which needs no import here
since no mole or mass concept is used.

The calibration line is the MF06 least-squares line of `MathlibExt.Probability.FiniteProbability`,
used directly: its slope and intercept are `olsSlope x y` and `olsIntercept x y`, they are the
unique minimizer of the residual sum of squares iff `Sxx > 0` (`ols_unique_minimizer_iff`), and
the residuals sum to zero and are orthogonal to `x` (`sum_resid_ols`, `sum_mul_resid_ols`). This
module adds no second name for any of them.

Section A proves Gauss-Markov unbiasedness in the finite-expectation form of MF06, for errors
with a finite distribution (the integral form is
`MathlibExt.Probability.Statistics.LinearModel.integral_olsEstimator_apply`, a different API),
covariance minimality of OLS among linear estimators by reusing
`MathlibExt.Probability.Statistics.GaussMarkov.gaussMarkov_covariance_minimality`, bridged from
its unit-noise form by scaling with `σ ^ 2`, and BLUE, which adds mean-zero errors to combine
the two. Section B defines inverse prediction `x₀ = (y₀ - a) / b`, proves the Fréchet derivative
of the three-input map `(y₀, a, b) ↦ x₀` for a nonzero slope `b`, and specializes the first-order
(GUM-style, CHEM-S6) law of propagation
`Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder` to that map, for random
inputs with finite second moments on a probability space. The result is the variance of the
linearization, never exact for the nonlinear map. Section C proves standard addition and
internal-standard drift cancellation.

## ii. Key results

- `expectation_olsEstimator_calibration`: the OLS estimators are unbiased in the
  finite-expectation sense.
- `calibration_covariance_minimality`: OLS has the smallest covariance among linear estimators
  `A *ᵥ y` with `A * X = 1`; no mean condition on the errors, so not BLUE by itself.
- `calibration_blue`: for a finite error distribution with mean-zero errors, OLS and every such
  estimator are unbiased and OLS has the smaller covariance (Gauss-Markov BLUE).
- `hasDerivAt_inversePredictionGradient`: for `b ≠ 0`, the gradient entries are the partial
  derivatives of inverse prediction.
- `hasFDerivAt_inversePredictionMap`: for `b ≠ 0`, the three-input inverse-prediction map has a
  Fréchet derivative whose coefficients are the gradient entries.
- `inversePrediction_linearizedVariance_firstOrder`: the variance of the first-order
  linearization of inverse prediction is the gradient-covariance sandwich.
- `inversePrediction_linearizedVariance_firstOrder_uncorrelated`: the explicit
  uncorrelated-inputs formula, including the response term `u(y₀) ^ 2 / b ^ 2`.
- `standardAdditionUnknown_eq`: the unknown is intercept over slope under zero-blank linear
  response.
- `internalStandardRatio_commonDrift`: a common multiplicative drift factor cancels in the
  analyte-to-standard ratio.

## iii. Table of contents

- A. Gauss-Markov unbiasedness and BLUE
- B. Inverse prediction and first-order uncertainty
- C. Standard addition and internal standard

## iv. References

- ATLAS CH24 planning anchors CHEM-S6 (JCGM 100:2008, _Guide to the Expression of Uncertainty
  in Measurement_) and CHEM-S1 (OpenStax _Chemistry 2e_). No other textbook source is used.
- `MathlibExt.Probability.FiniteProbability` (MF06 least-squares and finite-expectation API).
- `MathlibExt.Probability.Statistics.GaussMarkov.gaussMarkov_covariance_minimality`.
- `MathlibExt.Probability.Statistics.LinearModel.Sampling` (`olsMatrix`, `olsEstimator`).
- `Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder` and its uncorrelated
  specialization (first-order law of propagation of uncertainty).

## A. Gauss-Markov unbiasedness and BLUE
-/

@[expose] public section

open Matrix MathlibExt.Probability.FiniteProbability
  MathlibExt.Probability.Statistics.LinearModel MathlibExt.Probability.Statistics.GaussMarkov

namespace Chemistry.Calibration

/-- Expectation of an affine map of mean-zero errors: with `∑ ω, p ω = 1` and
`E[ε i] = 0` for every coordinate, `E[c j + (M *ᵥ ε) j] = c j`. Both unbiasedness proofs
below are applications of this MF06-expectation computation. -/
lemma expectation_const_add_mulVec {m : ℕ} {κ : Type*} {α : Type*} [Fintype α]
    (p : α → ℝ) (ε : α → Fin m → ℝ) (M : Matrix κ (Fin m) ℝ) (c : κ → ℝ)
    (hp1 : ∑ ω, p ω = 1) (hmean : ∀ i, expectation p (fun ω => ε ω i) = 0) (j : κ) :
    expectation p (fun ω => c j + (M *ᵥ ε ω) j) = c j := by
  rw [expectation_add, expectation_const hp1]
  suffices h : expectation p (fun ω => (M *ᵥ ε ω) j) = 0 by rw [h, add_zero]
  simp only [Matrix.mulVec, dotProduct]
  rw [expectation_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [expectation_const_mul, hmean i, mul_zero]

/-- **Unbiasedness of OLS** (CH24.3a). Under the Gauss-Markov model hypotheses, stated
explicitly: fixed design `X` with `IsUnit (Xᵀ * X)` (error-free `x`, including an intercept
column where the design has one), errors with a finite distribution `p` (`0 ≤ p ω` and
`∑ ω, p ω = 1`), the model equation `y ω = X *ᵥ β + ε ω`, and mean-zero errors `E[ε i] = 0` in
the MF06 finite-expectation sense, the OLS estimators satisfy `E[β̂ j] = β j` for the true
coefficient vector `β`, componentwise. The proof uses only `∑ ω, p ω = 1`. The hypothesis
`0 ≤ p ω` is still needed for the statement to be unbiasedness: MF06 defines a finite
distribution by both conditions, and for signed weights `expectation p` is not the mean under
any probability distribution. The integral form of this fact is `integral_olsEstimator_apply`;
this finite form is proved here. -/
lemma expectation_olsEstimator_calibration {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : IsUnit (Xᵀ * X)) {α : Type*} [Fintype α] (p : α → ℝ) (ε : α → Fin m → ℝ)
    (y : α → Fin m → ℝ) (β : Fin n → ℝ) (_hp0 : ∀ ω, 0 ≤ p ω)
    (hp1 : ∑ ω, p ω = 1) (hmean : ∀ i, expectation p (fun ω => ε ω i) = 0)
    (hmodel : ∀ ω, y ω = X *ᵥ β + ε ω) (j : Fin n) :
    expectation p (fun ω => olsEstimator X (y ω) j) = β j := by
  have hpt : ∀ ω, olsEstimator X (y ω) j = β j + (olsMatrix X *ᵥ ε ω) j := by
    intro ω
    rw [hmodel ω, olsEstimator_add hX β (ε ω)]
    rfl
  simp_rw [hpt]
  exact expectation_const_add_mulVec p ε (olsMatrix X) β hp1 hmean j

/-- **Unbiasedness of a linear estimator** (CH24.3a). Any estimator `β̃ ω = A *ᵥ y ω` whose
matrix satisfies the unbiasedness condition `A * X = 1` has `E[β̃ j] = β j` under the same
model hypotheses, including a finite error distribution `p` (`0 ≤ p ω` and `∑ ω, p ω = 1`). As
in `expectation_olsEstimator_calibration`, the proof uses only `∑ ω, p ω = 1`, and `0 ≤ p ω` is
what makes `expectation p` the mean under a probability distribution. -/
lemma expectation_linearUnbiased_calibration {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    {α : Type*} [Fintype α] (p : α → ℝ) (ε : α → Fin m → ℝ)
    (y : α → Fin m → ℝ) (β : Fin n → ℝ) (_hp0 : ∀ ω, 0 ≤ p ω)
    (hp1 : ∑ ω, p ω = 1) (hmean : ∀ i, expectation p (fun ω => ε ω i) = 0)
    (hmodel : ∀ ω, y ω = X *ᵥ β + ε ω)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : A * X = 1) (j : Fin n) :
    expectation p (fun ω => (A *ᵥ y ω) j) = β j := by
  have hpt : ∀ ω, (A *ᵥ y ω) j = β j + (A *ᵥ ε ω) j := by
    intro ω
    rw [hmodel ω, Matrix.mulVec_add, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
    rfl
  simp_rw [hpt]
  exact expectation_const_add_mulVec p ε A β hp1 hmean j

/-- A constant shift does not change the finite covariance matrix: with `∑ ω, p ω = 1`,
`covMatrix p (c + ε) = covMatrix p ε`. This bridges the model equation `y = Xβ + ε` to the
error covariance. -/
lemma covMatrix_add_const {m : ℕ} {α : Type*} [Fintype α] (p : α → ℝ)
    (ε : α → Fin m → ℝ) (c : Fin m → ℝ) (hp1 : ∑ ω, p ω = 1) :
    covMatrix p (fun ω => c + ε ω) = covMatrix p ε := by
  ext i j
  simp only [covMatrix_apply]
  have hEi : expectation p (fun ω => c i + ε ω i) =
      c i + expectation p (fun ω => ε ω i) := by
    rw [expectation_add, expectation_const hp1]
  have hEj : expectation p (fun ω => c j + ε ω j) =
      c j + expectation p (fun ω => ε ω j) := by
    rw [expectation_add, expectation_const hp1]
  simp only [covariance, Pi.add_apply, hEi, hEj]
  congr 1
  funext ω
  ring

/-- **Covariance minimality of OLS** (CH24.3b). Under fixed design `X` with
`IsUnit (Xᵀ * X)`, the model equation `y ω = X *ᵥ β + ε ω`, and homoscedastic uncorrelated
errors `covMatrix p ε = σ ^ 2 • 1` in finite matrix form, any linear estimator
`β̃ ω = A *ᵥ y ω` with `A * X = 1` has covariance at least that of OLS: the difference of the
covariance matrices is positive semidefinite. No mean condition on `ε` is assumed, so this is
covariance minimality only: without `E[ε] = 0` neither estimator need be unbiased. BLUE is
`calibration_blue`, which adds mean-zero errors and a finite error distribution (`0 ≤ p`). The
comparison itself is algebraic and uses only `∑ ω, p ω = 1`. The covariance-minimality step is
`gaussMarkov_covariance_minimality`, reused; the bridge from its unit-noise form is the exact
scaling by `σ ^ 2`. -/
theorem calibration_covariance_minimality {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : IsUnit (Xᵀ * X)) {α : Type*} [Fintype α] (p : α → ℝ) (ε : α → Fin m → ℝ)
    (σ : ℝ) (hp1 : ∑ ω, p ω = 1) (hcov : covMatrix p ε = σ ^ 2 • 1)
    (y : α → Fin m → ℝ) (β : Fin n → ℝ) (hmodel : ∀ ω, y ω = X *ᵥ β + ε ω)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : A * X = 1) :
    (covMatrix p (fun ω => A *ᵥ y ω) - covMatrix p (fun ω => olsEstimator X (y ω))).PosSemidef := by
  have hY : y = fun ω => (X *ᵥ β) + ε ω := funext hmodel
  have hcovY : covMatrix p y = covMatrix p ε := by
    rw [hY]
    exact covMatrix_add_const p ε (X *ᵥ β) hp1
  have hcovA : covMatrix p (fun ω => A *ᵥ y ω) = σ ^ 2 • (A * Aᵀ) := by
    rw [covMatrix_mulVec, hcovY, hcov, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hcovB : covMatrix p (fun ω => olsEstimator X (y ω)) =
      σ ^ 2 • (olsMatrix X * (olsMatrix X)ᵀ) := by
    have heq : (fun ω => olsEstimator X (y ω)) = (fun ω => olsMatrix X *ᵥ y ω) := rfl
    rw [heq, covMatrix_mulVec, hcovY, hcov, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  obtain ⟨-, hmin⟩ := gaussMarkov_covariance_minimality X hX
  have hpsd := hmin A hA
  rw [hcovA, hcovB, olsMatrix_eq, ← smul_sub]
  exact hpsd.smul (sq_nonneg σ)

/-- **Gauss-Markov: OLS is BLUE** (CH24.3b). Under the Gauss-Markov model hypotheses, stated
explicitly: fixed design `X` with `IsUnit (Xᵀ * X)`, errors with a finite distribution `p`
(`0 ≤ p ω` and `∑ ω, p ω = 1`), the model equation `y ω = X *ᵥ β + ε ω`, mean-zero errors
`E[ε i] = 0` in the MF06 finite-expectation sense, and homoscedastic uncorrelated errors
`covMatrix p ε = σ ^ 2 • 1`: OLS is unbiased, every linear estimator `β̃ ω = A *ᵥ y ω` with
`A * X = 1` is unbiased, and the covariance of `β̃` exceeds that of OLS by a positive
semidefinite matrix. The hypothesis `0 ≤ p ω` makes `p` a probability distribution, without
which "unbiased" and "best" have no probabilistic meaning; it is threaded to the two
unbiasedness lemmas. This combines `expectation_olsEstimator_calibration`,
`expectation_linearUnbiased_calibration` and `calibration_covariance_minimality`. -/
theorem calibration_blue {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : IsUnit (Xᵀ * X)) {α : Type*} [Fintype α] (p : α → ℝ) (ε : α → Fin m → ℝ)
    (σ : ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (hmean : ∀ i, expectation p (fun ω => ε ω i) = 0)
    (hcov : covMatrix p ε = σ ^ 2 • 1)
    (y : α → Fin m → ℝ) (β : Fin n → ℝ) (hmodel : ∀ ω, y ω = X *ᵥ β + ε ω)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : A * X = 1) :
    (∀ j, expectation p (fun ω => olsEstimator X (y ω) j) = β j) ∧
      (∀ j, expectation p (fun ω => (A *ᵥ y ω) j) = β j) ∧
      (covMatrix p (fun ω => A *ᵥ y ω) -
        covMatrix p (fun ω => olsEstimator X (y ω))).PosSemidef :=
  ⟨expectation_olsEstimator_calibration X hX p ε y β hp0 hp1 hmean hmodel,
    expectation_linearUnbiased_calibration X p ε y β hp0 hp1 hmean hmodel A hA,
    calibration_covariance_minimality X hX p ε σ hp1 hcov y β hmodel A hA⟩

/-! ## B. Inverse prediction and first-order uncertainty -/

/-- Inverse prediction from a fitted line (CH24.4): given fitted intercept `a`, fitted slope
`b` and a new response `y₀`, the predicted concentration is `x₀ = (y₀ - a) / b`. No Mathlib
or ATLAS definition covers fitted-line inverse prediction (`EarthScience` treats a known
line with the fitted case explicitly out of scope). -/
noncomputable def inversePrediction (a b y₀ : ℝ) : ℝ :=
  (y₀ - a) / b

/-- The exact algebraic identity for inverse prediction: `b * x₀ + a = y₀` for `b ≠ 0`. This
is definition unfolding, kept separate so the first-order uncertainty formula below is never
confused with the definition. -/
lemma inversePrediction_mul (a b y₀ : ℝ) (hb : b ≠ 0) :
    b * inversePrediction a b y₀ + a = y₀ := by
  simp only [inversePrediction]
  field_simp
  ring

/-- The gradient of inverse prediction with respect to `(y₀, a, b)` (CH24.4): the partial
derivatives `1 / b`, `-1 / b` and `-(y₀ - a) / b ^ 2`. For `b ≠ 0` they are the derivatives of
the one-variable slices (`hasDerivAt_inversePredictionGradient`) and the coefficients of the
Fréchet derivative of the three-input map (`hasFDerivAt_inversePredictionMap`). At `b = 0`
inverse prediction is undefined and the slope derivative does not exist; Lean's totalized
division makes all three entries `0` there, which is not a gradient, so every lemma that treats
this vector as the gradient requires `b ≠ 0`. This is an explicit `3`-vector of sensitivity
coefficients, not Mathlib's inner-product-space gradient, whose Hilbert-space setup the
first-order law does not need. -/
noncomputable def inversePredictionGradient (a b y₀ : ℝ) : Fin 3 → ℝ :=
  ![1 / b, -1 / b, -(y₀ - a) / b ^ 2]

/-- First gradient component. -/
lemma inversePredictionGradient_zero (a b y₀ : ℝ) :
    inversePredictionGradient a b y₀ 0 = 1 / b := by
  simp [inversePredictionGradient]

/-- Second gradient component. -/
lemma inversePredictionGradient_one (a b y₀ : ℝ) :
    inversePredictionGradient a b y₀ 1 = -1 / b := by
  simp [inversePredictionGradient]

/-- Third gradient component. -/
lemma inversePredictionGradient_two (a b y₀ : ℝ) :
    inversePredictionGradient a b y₀ 2 = -(y₀ - a) / b ^ 2 := by
  simp [inversePredictionGradient]

/-- Partial derivative of inverse prediction with respect to the new response `y₀`. -/
lemma hasDerivAt_inversePrediction_response (a b y₀ : ℝ) :
    HasDerivAt (fun t => inversePrediction a b t) (1 / b) y₀ := by
  simp only [inversePrediction]
  exact ((hasDerivAt_id y₀).sub_const a).div_const b

/-- Partial derivative of inverse prediction with respect to the fitted intercept `a`. -/
lemma hasDerivAt_inversePrediction_intercept (a b y₀ : ℝ) :
    HasDerivAt (fun t => inversePrediction t b y₀) (-1 / b) a := by
  simp only [inversePrediction]
  exact ((hasDerivAt_id a).const_sub y₀).div_const b

/-- Partial derivative of inverse prediction with respect to the fitted slope `b`, at
`b ≠ 0`. -/
lemma hasDerivAt_inversePrediction_slope (a y₀ : ℝ) {b : ℝ} (hb : b ≠ 0) :
    HasDerivAt (fun t => inversePrediction a t y₀) (-(y₀ - a) / b ^ 2) b := by
  simp only [inversePrediction]
  have hder : -(y₀ - a) / b ^ 2 = (0 * b - (y₀ - a) * 1) / b ^ 2 := by ring
  rw [hder]
  exact (hasDerivAt_const b (y₀ - a)).div (hasDerivAt_id b) hb

/-- For a nonzero slope `b`, the entries of `inversePredictionGradient a b y₀` are the partial
derivatives of inverse prediction with respect to `y₀`, `a` and `b`. -/
lemma hasDerivAt_inversePredictionGradient (a y₀ : ℝ) {b : ℝ} (hb : b ≠ 0) :
    HasDerivAt (fun t => inversePrediction a b t) (inversePredictionGradient a b y₀ 0) y₀ ∧
      HasDerivAt (fun t => inversePrediction t b y₀) (inversePredictionGradient a b y₀ 1) a ∧
      HasDerivAt (fun t => inversePrediction a t y₀) (inversePredictionGradient a b y₀ 2) b := by
  rw [inversePredictionGradient_zero, inversePredictionGradient_one,
    inversePredictionGradient_two]
  exact ⟨hasDerivAt_inversePrediction_response a b y₀,
    hasDerivAt_inversePrediction_intercept a b y₀, hasDerivAt_inversePrediction_slope a y₀ hb⟩

/-- Inverse prediction as a function of its three inputs `v = (y₀, a, b)`, indexed `0`, `1`, `2`
in the order of `inversePredictionGradient`: `inversePredictionMap v = (v 0 - v 1) / v 2`. This
is the measurement function to which the first-order law of propagation applies. -/
noncomputable def inversePredictionMap (v : Fin 3 → ℝ) : ℝ :=
  inversePrediction (v 1) (v 2) (v 0)

/-- **Fréchet derivative of inverse prediction** (CH24.4). For a nonzero slope `b`, the
three-input map `inversePredictionMap` has Fréchet derivative `h ↦ ∑ i, gᵢ * h i` at the input
estimate `(y₀, a, b)`, where `g = inversePredictionGradient a b y₀`. This is the multivariate
statement; `hasDerivAt_inversePredictionGradient` gives only the one-variable slices. At `b = 0`
inverse prediction is undefined and the map is not differentiable. -/
lemma hasFDerivAt_inversePredictionMap (a y₀ : ℝ) {b : ℝ} (hb : b ≠ 0) :
    HasFDerivAt inversePredictionMap
      (∑ i, inversePredictionGradient a b y₀ i •
        (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)) ![y₀, a, b] := by
  have hnum : HasFDerivAt (fun v : Fin 3 → ℝ => v 0 - v 1)
      ((ContinuousLinearMap.proj 0 : (Fin 3 → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj 1)
      ![y₀, a, b] :=
    (hasFDerivAt_apply 0 _).sub (hasFDerivAt_apply 1 _)
  have hden : HasFDerivAt (fun v : Fin 3 → ℝ => (v 2)⁻¹)
      ((-(b ^ 2)⁻¹) • (ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ)) ![y₀, a, b] :=
    (hasDerivAt_inv hb).comp_hasFDerivAt (f := fun v : Fin 3 → ℝ => v 2) ![y₀, a, b]
      (hasFDerivAt_apply 2 _)
  have hmap : inversePredictionMap = fun v : Fin 3 → ℝ => (v 0 - v 1) * (v 2)⁻¹ := by
    funext v
    simp only [inversePredictionMap, inversePrediction, div_eq_mul_inv]
  rw [hmap]
  convert hnum.fun_mul hden using 1
  refine ContinuousLinearMap.ext fun h => ?_
  simp [Fin.sum_univ_three, inversePredictionGradient]
  field_simp
  ring

/-- The sensitivity coefficients of inverse prediction: for `b ≠ 0`, the partial derivative of
`inversePredictionMap` at `(y₀, a, b)` along the `i`-th input is the gradient entry
`inversePredictionGradient a b y₀ i`. -/
lemma fderiv_inversePredictionMap_single (a y₀ : ℝ) {b : ℝ} (hb : b ≠ 0) (i : Fin 3) :
    fderiv ℝ inversePredictionMap ![y₀, a, b] (Pi.single i 1) =
      inversePredictionGradient a b y₀ i := by
  rw [(hasFDerivAt_inversePredictionMap a y₀ hb).fderiv]
  simp [Pi.single_apply]

section FirstOrderUncertainty

open MeasureTheory
open scoped ProbabilityTheory

/-- **First-order uncertainty of inverse prediction** (CH24.4). For a nonzero slope `b`, let the
inputs `(y₀, a, b)` be random variables `X 0`, `X 1`, `X 2` with finite second moments on a
probability space, with estimate `![y₀, a, b]`. The first-order linearization of
`inversePredictionMap` at the estimate, built from its Fréchet derivative, has variance
`∑ i, ∑ j, gᵢ * gⱼ * cov[X i, X j]`, where `g = inversePredictionGradient a b y₀`. This is
`Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder` applied to
`hasFDerivAt_inversePredictionMap`. It is a GUM-style (CHEM-S6) linearization: exact for the
linearization, never for the nonlinear map `(y₀, a, b) ↦ x₀`. -/
lemma inversePrediction_linearizedVariance_firstOrder {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (a y₀ : ℝ) {b : ℝ} (hb : b ≠ 0)
    (X : Fin 3 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[fun ω => inversePredictionMap ![y₀, a, b] +
        fderiv ℝ inversePredictionMap ![y₀, a, b] (fun i => X i ω - ![y₀, a, b] i); μ] =
      ∑ i, ∑ j, inversePredictionGradient a b y₀ i * inversePredictionGradient a b y₀ j *
        cov[X i, X j; μ] := by
  rw [Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder
    (hasFDerivAt_inversePredictionMap a y₀ hb).differentiableAt.hasFDerivAt X hX]
  simp only [fderiv_inversePredictionMap_single a y₀ hb]

/-- **First-order uncertainty of inverse prediction, uncorrelated inputs** (CH24.4). For a
nonzero slope `b` and random inputs `X 0`, `X 1`, `X 2` for `(y₀, a, b)` that are pairwise
uncorrelated, with standard uncertainties `u 0`, `u 1`, `u 2` (`Var[X i] = u i ^ 2`), the
variance of the first-order linearization of `inversePredictionMap` at `(y₀, a, b)` is
`(u 0 ^ 2 + u 1 ^ 2) / b ^ 2 + (y₀ - a) ^ 2 / b ^ 4 * u 2 ^ 2`, including the
response-uncertainty term `u(y₀) ^ 2 / b ^ 2`. This is
`Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder_uncorrelated` with the
sensitivity coefficients of `fderiv_inversePredictionMap_single`. -/
lemma inversePrediction_linearizedVariance_firstOrder_uncorrelated {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (a y₀ : ℝ) {b : ℝ}
    (hb : b ≠ 0) (X : Fin 3 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (u : Fin 3 → ℝ)
    (hu : ∀ i, Var[X i; μ] = u i ^ 2) (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    Var[fun ω => inversePredictionMap ![y₀, a, b] +
        fderiv ℝ inversePredictionMap ![y₀, a, b] (fun i => X i ω - ![y₀, a, b] i); μ] =
      (u 0 ^ 2 + u 1 ^ 2) / b ^ 2 + (y₀ - a) ^ 2 / b ^ 4 * u 2 ^ 2 := by
  rw [Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder_uncorrelated
    (hasFDerivAt_inversePredictionMap a y₀ hb).differentiableAt.hasFDerivAt X hX u hu hcov]
  simp only [Fin.sum_univ_three, fderiv_inversePredictionMap_single a y₀ hb,
    inversePredictionGradient_zero, inversePredictionGradient_one, inversePredictionGradient_two]
  field_simp

end FirstOrderUncertainty

/-! ## C. Standard addition and internal standard -/

/-- Standard-addition unknown from a fitted line (CH24.5a): given the fitted intercept and
slope of the response-versus-added-concentration line, the unknown concentration is
`intercept / slope`. The parametrization is fixed once here: `intercept` and `slope` are the
fitted line's coefficients, and the sign convention is that the line `y = a + b * t` meets
`y = 0` at `t = -a / b`, so the unknown is `-t* = a / b` (positive for same-sign `a, b`).
No Mathlib or ATLAS definition covers standard addition. -/
noncomputable def standardAdditionUnknown (intercept slope : ℝ) : ℝ :=
  intercept / slope

/-- Standard addition with an explicit blank (CH24.5a): under the linear-response model
`y s = a₀ + b * (x_u + s)` with the same blank `a₀` and sensitivity `b` for all additions,
and the fitted line `y s = a + b * s` exact in the model, the unknown is
`x_u = (a - a₀) / b`. -/
lemma standardAddition_unknown_eq (x_u a₀ a b : ℝ) (t : ℝ) (y : ℝ → ℝ)
    (hmodel : ∀ s, y s = a₀ + b * (x_u + s))
    (hfill : ∀ s, y s = a + b * s)
    (hb : b ≠ 0) :
    x_u = (a - a₀) / b := by
  have h : a + b * t = a₀ + b * (x_u + t) := (hfill t).symm.trans (hmodel t)
  have h2 : a - a₀ = b * x_u := by linarith
  rw [h2]
  field_simp

/-- Standard addition (CH24.5a): under zero-blank linear response `y s = b * (x_u + s)` with
the same sensitivity `b` for all additions, and the fitted line `y s = a + b * s` exact in
the model, the unknown is the fitted intercept over the fitted slope. -/
lemma standardAdditionUnknown_eq (x_u a b : ℝ) (t : ℝ) (y : ℝ → ℝ)
    (hmodel : ∀ s, y s = b * (x_u + s))
    (hfill : ∀ s, y s = a + b * s)
    (hb : b ≠ 0) :
    standardAdditionUnknown a b = x_u := by
  have h : a + b * t = b * (x_u + t) := (hfill t).symm.trans (hmodel t)
  have h2 : a = b * x_u := by linarith
  simp only [standardAdditionUnknown]
  rw [h2]
  field_simp

/-- Internal-standard ratio (CH24.5b): the analyte response over the standard response. No
Mathlib or ATLAS definition covers internal-standard ratios. -/
noncomputable def internalStandardRatio (y_analyte y_standard : ℝ) : ℝ :=
  y_analyte / y_standard

/-- A common multiplicative drift factor cancels in the internal-standard ratio (CH24.5b):
with `d ≠ 0`, `(d * y_a) / (d * y_s) = y_a / y_s`. -/
lemma internalStandardRatio_commonDrift (ya0 ys0 d : ℝ) (hd : d ≠ 0) (hys : ys0 ≠ 0) :
    internalStandardRatio (d * ya0) (d * ys0) = internalStandardRatio ya0 ys0 := by
  simp only [internalStandardRatio]
  field_simp

/-- Independent drift factors do not cancel (CH24.5b): the drifted ratio is the drift ratio
times the undrifted ratio, `(d₁ / d₂) * R⁰`. -/
lemma internalStandardRatio_independentDrift (ya0 ys0 d₁ d₂ : ℝ) (hd₂ : d₂ ≠ 0)
    (hys : ys0 ≠ 0) :
    internalStandardRatio (d₁ * ya0) (d₂ * ys0) =
      (d₁ / d₂) * internalStandardRatio ya0 ys0 := by
  simp only [internalStandardRatio]
  field_simp

/-- The independent-drift ratio differs from the undrifted ratio in general (CH24.5b): with
`d₁ ≠ d₂` and nonzero ratio, cancellation fails. -/
lemma internalStandardRatio_independentDrift_ne (ya0 ys0 d₁ d₂ : ℝ) (hd₂ : d₂ ≠ 0)
    (hys : ys0 ≠ 0) (hd : d₁ ≠ d₂) (hR : ya0 / ys0 ≠ 0) :
    internalStandardRatio (d₁ * ya0) (d₂ * ys0) ≠ internalStandardRatio ya0 ys0 := by
  rw [internalStandardRatio_independentDrift ya0 ys0 d₁ d₂ hd₂ hys]
  simp only [internalStandardRatio] at hR ⊢
  intro hcon
  have h1 : d₁ / d₂ = 1 := mul_right_cancel₀ hR (by rw [hcon, one_mul])
  have h2 : d₁ = d₂ := by
    field_simp at h1
    linarith
  exact hd h2

end Chemistry.Calibration
