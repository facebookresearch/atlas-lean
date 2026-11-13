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

/-!
# Analytical calibration: regression, figures of merit and inverse prediction

Calibration lines from standard data: ordinary least squares as a thin specialization of MF06,
Gauss-Markov unbiasedness and BLUE, first-order inverse-prediction uncertainty, standard addition
and internal standards.

## i. Overview

Calibration data are finitely many pairs `(x i, y i)`, where `x i` is the known concentration of
standard `i` and `y i` is the measured response. That `x` is error-free is a MODEL hypothesis,
stated explicitly where it is used. The calibration line is an empirical fit with no truth claim:
no statement below asserts that the true response is linear, and the line carries no validity
outside the calibrated range (extrapolation gets no theorem). A near-`1` `R²` proves nothing about
linearity; `R²` is not defined or used here. Concentrations and responses are real numbers after a
consistent choice of units, the convention of `Chemistry.Amounts`, which needs no import here
since no mole or mass concept is used.

Section A specializes the MF06 least-squares API
(`MathlibExt.Probability.FiniteProbability`): `calibrationSlope` and `calibrationIntercept` are
pure aliases of `olsSlope` and `olsIntercept`, and the unique-minimizer, residual-sum and
residual-orthogonality statements are the MF06 lemmas `ols_unique_minimizer_iff`, `sum_resid_ols`
and `sum_mul_resid_ols`, applied, not re-derived. Section B proves Gauss-Markov unbiasedness in
the finite-expectation form of MF06 (the integral form is
`MathlibExt.Probability.Statistics.LinearModel.integral_olsEstimator_apply`, a different API),
covariance minimality of OLS among linear estimators by reusing
`MathlibExt.Probability.Statistics.GaussMarkov.gaussMarkov_covariance_minimality`, bridged from
its unit-noise form by scaling with `σ ^ 2`, and BLUE, which adds mean-zero errors to combine
the two. Section C defines inverse prediction `x₀ = (y₀ - a) / b` for a nonzero slope `b` and
proves its first-order (GUM-style, CHEM-S6) uncertainty propagation, labelled as a
linearization and never exact for the nonlinear map `(y₀, a, b) ↦ x₀`. Section D
proves standard addition and internal-standard drift cancellation.

## ii. Key results

- `calibration_unique_minimizer_iff`: the calibration slope and intercept are the unique
  minimizer of the residual sum of squares iff `Sxx > 0` (MF06, applied).
- `calibration_sum_resid`, `calibration_sum_mul_resid`: calibration residuals sum to zero and
  are orthogonal to `x` (MF06, applied).
- `expectation_olsEstimator_calibration`: the OLS estimators are unbiased in the
  finite-expectation sense.
- `calibration_covariance_minimality`: OLS has the smallest covariance among linear estimators
  `A *ᵥ y` with `A * X = 1`; no mean condition on the errors, so not BLUE by itself.
- `calibration_blue`: under mean-zero errors, OLS and every such estimator are unbiased and OLS
  has the smaller covariance (Gauss-Markov BLUE).
- `variance_firstOrderInversePrediction`: the variance of the linearized inverse-prediction map
  is the gradient-covariance sandwich.
- `hasDerivAt_inversePredictionGradient`: for `b ≠ 0`, the gradient entries are the partial
  derivatives of inverse prediction.
- `firstOrderInversePredictionVariance_gradient_diagonal`: the explicit uncorrelated-inputs
  formula for `b ≠ 0`, including the response term `u(y₀) ^ 2 / b ^ 2`.
- `standardAdditionUnknown_eq`: the unknown is intercept over slope under zero-blank linear
  response.
- `internalStandardRatio_commonDrift`: a common multiplicative drift factor cancels in the
  analyte-to-standard ratio.

## iii. Table of contents

- A. Calibration slope, intercept and residuals (MF06 specialization)
- B. Gauss-Markov unbiasedness and BLUE
- C. Inverse prediction and first-order uncertainty
- D. Standard addition and internal standard

## iv. References

- ATLAS MF06 planning anchors CHEM-S6 (JCGM 100:2008, _Guide to the Expression of Uncertainty
  in Measurement_) and CHEM-S1 (OpenStax _Chemistry 2e_). No other textbook source is used.
- `MathlibExt.Probability.FiniteProbability` (MF06 least-squares API).
- `MathlibExt.Probability.Statistics.GaussMarkov.gaussMarkov_covariance_minimality`.
- `MathlibExt.Probability.Statistics.LinearModel.Sampling` (`olsMatrix`, `olsEstimator`).

## A. Calibration slope, intercept and residuals (MF06 specialization)
-/

@[expose] public section

open Matrix MathlibExt.Probability.FiniteProbability
  MathlibExt.Probability.Statistics.LinearModel MathlibExt.Probability.Statistics.GaussMarkov

namespace Chemistry.Calibration

/-- The calibration slope of responses `y` on standard concentrations `x` (CH24.1). This is a
pure alias of the MF06 least-squares slope `olsSlope`; there is no second OLS implementation.
`calibrationSlope_eq` records the alias. -/
noncomputable def calibrationSlope {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  olsSlope x y

/-- The calibration intercept of responses `y` on standard concentrations `x` (CH24.1). This is
a pure alias of the MF06 least-squares intercept `olsIntercept`; `calibrationIntercept_eq`
records the alias. -/
noncomputable def calibrationIntercept {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  olsIntercept x y

/-- `calibrationSlope` is the MF06 slope. -/
lemma calibrationSlope_eq {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    calibrationSlope x y = olsSlope x y :=
  rfl

/-- `calibrationIntercept` is the MF06 intercept. -/
lemma calibrationIntercept_eq {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    calibrationIntercept x y = olsIntercept x y :=
  rfl

/-- **Calibration line.** The calibration intercept and slope minimize the residual sum of
squares, and every minimizer equals them, if and only if `0 < Sxx` (CH24.1). This is the MF06
lemma `ols_unique_minimizer_iff`, applied. -/
lemma calibration_unique_minimizer_iff {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    (∀ a b, rssLine x y (calibrationIntercept x y) (calibrationSlope x y) ≤ rssLine x y a b ∧
      (rssLine x y a b ≤ rssLine x y (calibrationIntercept x y) (calibrationSlope x y) →
        a = calibrationIntercept x y ∧ b = calibrationSlope x y)) ↔ 0 < sxy x x :=
  ols_unique_minimizer_iff x y

/-- The calibration residuals sum to zero: orthogonality to the constant vector (CH24.2). This
is the MF06 lemma `sum_resid_ols`, applied. -/
lemma calibration_sum_resid {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    ∑ i, (y i - (calibrationIntercept x y + calibrationSlope x y * x i)) = 0 :=
  sum_resid_ols x y

/-- The calibration residuals are orthogonal to the standard concentrations `x` (CH24.2). This
is the MF06 lemma `sum_mul_resid_ols`, applied. -/
lemma calibration_sum_mul_resid {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    ∑ i, x i * (y i - (calibrationIntercept x y + calibrationSlope x y * x i)) = 0 :=
  sum_mul_resid_ols x y

/-! ## B. Gauss-Markov unbiasedness and BLUE -/

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
column where the design has one), the model equation `y ω = X *ᵥ β + ε ω`, and mean-zero
errors `E[ε i] = 0` in the MF06 finite-expectation sense, the OLS estimators satisfy
`E[β̂ j] = β j` for the true coefficient vector `β`, componentwise. The integral form of this
fact is `integral_olsEstimator_apply`; this finite form is proved here. -/
lemma expectation_olsEstimator_calibration {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : IsUnit (Xᵀ * X)) {α : Type*} [Fintype α] (p : α → ℝ) (ε : α → Fin m → ℝ)
    (y : α → Fin m → ℝ) (β : Fin n → ℝ)
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
model hypotheses. -/
lemma expectation_linearUnbiased_calibration {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    {α : Type*} [Fintype α] (p : α → ℝ) (ε : α → Fin m → ℝ)
    (y : α → Fin m → ℝ) (β : Fin n → ℝ)
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
`calibration_blue`, which adds mean-zero errors. The covariance-minimality step is
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
explicitly: fixed design `X` with `IsUnit (Xᵀ * X)`, the model equation `y ω = X *ᵥ β + ε ω`,
mean-zero errors `E[ε i] = 0` in the MF06 finite-expectation sense, and homoscedastic
uncorrelated errors `covMatrix p ε = σ ^ 2 • 1`: OLS is unbiased, every linear estimator
`β̃ ω = A *ᵥ y ω` with `A * X = 1` is unbiased, and the covariance of `β̃` exceeds that of OLS
by a positive semidefinite matrix. This combines `expectation_olsEstimator_calibration`,
`expectation_linearUnbiased_calibration` and `calibration_covariance_minimality`. -/
theorem calibration_blue {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : IsUnit (Xᵀ * X)) {α : Type*} [Fintype α] (p : α → ℝ) (ε : α → Fin m → ℝ)
    (σ : ℝ) (hp1 : ∑ ω, p ω = 1) (hmean : ∀ i, expectation p (fun ω => ε ω i) = 0)
    (hcov : covMatrix p ε = σ ^ 2 • 1)
    (y : α → Fin m → ℝ) (β : Fin n → ℝ) (hmodel : ∀ ω, y ω = X *ᵥ β + ε ω)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : A * X = 1) :
    (∀ j, expectation p (fun ω => olsEstimator X (y ω) j) = β j) ∧
      (∀ j, expectation p (fun ω => (A *ᵥ y ω) j) = β j) ∧
      (covMatrix p (fun ω => A *ᵥ y ω) -
        covMatrix p (fun ω => olsEstimator X (y ω))).PosSemidef :=
  ⟨expectation_olsEstimator_calibration X hX p ε y β hp1 hmean hmodel,
    expectation_linearUnbiased_calibration X p ε y β hp1 hmean hmodel A hA,
    calibration_covariance_minimality X hX p ε σ hp1 hcov y β hmodel A hA⟩

/-! ## C. Inverse prediction and first-order uncertainty -/

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
derivatives `1 / b`, `-1 / b` and `-(y₀ - a) / b ^ 2`, proved for `b ≠ 0` in
`hasDerivAt_inversePredictionGradient`. At `b = 0` inverse prediction is undefined and the
slope derivative does not exist; Lean's totalized division makes all three entries `0` there,
which is not a gradient, so every lemma that treats this vector as the gradient requires
`b ≠ 0`. This is an explicit `3`-vector for the finite-sum sandwich, not Mathlib's
inner-product-space gradient, whose Hilbert-space setup the sandwich does not need. -/
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

/-- First-order propagated variance of inverse prediction (CH24.4): the gradient-covariance
sandwich `∑ i, ∑ j, c i * c j * V i j` for coefficients `c` and input covariance matrix `V`.
This is a GUM-style (CHEM-S6) linearization, never exact for the nonlinear map
`(y₀, a, b) ↦ x₀`. No GUM propagation API exists on ATLAS `main` (CH02 is not merged), so the
sandwich is stated and proved here from MF06 bilinearity. -/
noncomputable def inversePredictionFirstOrderVariance (c : Fin 3 → ℝ)
    (V : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * V i j

/-- The variance of the linearized inverse-prediction map is exactly the first-order sandwich
(CH24.4): for random inputs `X` with `∑ ω, p ω = 1`, the affine map
`K + ∑ i, c i * X i` has finite variance `∑ i, ∑ j, c i * c j * Cov(X i, X j)`, by the MF06
bilinearity lemma `covariance_sum_mul_sum`. Exact for the linearization; the nonlinear map's
true variance is only approximated by it. -/
lemma variance_firstOrderInversePrediction {α : Type*} [Fintype α] (p : α → ℝ)
    (X : α → Fin 3 → ℝ) (c : Fin 3 → ℝ) (K : ℝ) (hp1 : ∑ ω, p ω = 1) :
    variance p (fun ω => K + ∑ i, c i * X ω i) =
      inversePredictionFirstOrderVariance c (covMatrix p X) := by
  have h1 : (fun ω => K + ∑ i, c i * X ω i) =
      (fun ω => 1 * (∑ i, c i * X ω i) + K) := by
    funext ω
    ring
  rw [h1, variance_affine hp1 _ 1 K, one_pow, one_mul, ← covariance_self,
    covariance_sum_mul_sum]
  simp only [inversePredictionFirstOrderVariance, covMatrix_apply]

/-- Explicit first-order formula for uncorrelated inputs (CH24.4): for a nonzero slope `b`,
with the proven gradient and a diagonal input covariance matrix (`V i i` the input variances,
off-diagonals zero), the linearized variance is
`(u2y + u2a) / b ^ 2 + (y₀ - a) ^ 2 / b ^ 4 * u2b`, including the response-uncertainty term
`u(y₀) ^ 2 / b ^ 2`. The algebra does not use `b ≠ 0`; the hypothesis restricts the formula to
slopes where the gradient exists, so a zero-slope calibration gets no uncertainty from it. -/
lemma firstOrderInversePredictionVariance_gradient_diagonal (a b y₀ : ℝ) (_hb : b ≠ 0)
    (V : Matrix (Fin 3) (Fin 3) ℝ) (u2y u2a u2b : ℝ)
    (h00 : V 0 0 = u2y) (h11 : V 1 1 = u2a) (h22 : V 2 2 = u2b)
    (hoff : ∀ i j, i ≠ j → V i j = 0) :
    inversePredictionFirstOrderVariance (inversePredictionGradient a b y₀) V =
      (u2y + u2a) / b ^ 2 + (y₀ - a) ^ 2 / b ^ 4 * u2b := by
  simp only [inversePredictionFirstOrderVariance, Fin.sum_univ_three,
    inversePredictionGradient_zero, inversePredictionGradient_one,
    inversePredictionGradient_two]
  rw [hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide),
    hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide),
    h00, h11, h22]
  ring

/-! ## D. Standard addition and internal standard -/

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
