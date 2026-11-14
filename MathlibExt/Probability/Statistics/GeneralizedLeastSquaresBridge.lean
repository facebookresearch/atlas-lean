/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import MathlibExt.Biology.StatisticalGenetics.MixedModel
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# GLS bridge: estimator law, mixed-model covariance, and BLUP versus BLUE

For a design matrix `X` and positive-definite noise covariance `V`, the GLS
estimator `β̂ = glsMatrix X V *ᵥ y` is unbiased with covariance
`(Xᵀ V⁻¹ X)⁻¹`, and full column rank of `X` supplies the invertibility
hypothesis used by `MathlibExt.Probability.Statistics.GeneralizedLeastSquares`.
With `V = Z G Zᵀ + R` (`phenCov`), this is the covariance of the mixed-model
marginal law, and Henderson's equations pick out the same `β̂`
(`isMMESolution_iff_gls`).

Estimation and prediction are separate obligations with distinct hypotheses.
Unbiased estimation of the fixed effects `β` asks `B * X = 1`; best linear
unbiased prediction of the random effects asks `L * X = 0`, and the BLUP
weights `L = G Zᵀ V⁻¹ (1 - X B)` minimize the mean-squared-error matrix
`C ↦ C V Cᵀ - C Z G - G Zᵀ Cᵀ + G` among all weight matrices with `C * X = 0`.

## Main results

* `glsEstimator`: the GLS estimate `(Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y`.
* `isUnit_XtVinvX_of_linearIndependent`: full column rank plus `V.PosDef`
  give `IsUnit (Xᵀ * V⁻¹ * X)`.
* `integral_glsEstimator_apply`, `integral_glsEstimator`: unbiasedness.
* `covariance_glsEstimator`: covariance `(Xᵀ V⁻¹ X)⁻¹`.
* `mixed_glsEstimator_unbiased`, `mixed_glsEstimator_covariance`: the same
  with `V = phenCov Z G R`, stating the `G`/`R`/`V` dimensions.
* `isMMESolution_iff_glsEstimator`: Henderson solutions carry `glsEstimator`.
* `blupMatrix`: the BLUP weights `G Zᵀ V⁻¹ (1 - X B)`.
* `blupMatrix_mul_X`: prediction weights annihilate `X` (`L * X = 0`).
* `blupPredictionError_eq`: the prediction error is free of `β`.
* `blup_mse_minimality`: MSE-matrix minimality among `C` with `C * X = 0`.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares
open MathlibExt.Biology.StatisticalGenetics.MixedModel

namespace MathlibExt.Probability.Statistics.GeneralizedLeastSquaresBridge

/-- The GLS estimate of `β` in `y = X β + ε` with noise covariance `V`:
`β̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y`. -/
noncomputable def glsEstimator {n p : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] (X : Matrix n p ℝ) (V : Matrix n n ℝ)
    (y : n → ℝ) : p → ℝ :=
  glsMatrix X V *ᵥ y

/-- The BLUP weight matrix for the random effects: with `B = glsMatrix X V`,
`L = G Zᵀ V⁻¹ (1 - X B)` predicts `u` from `y = X β + Z u + e`. -/
noncomputable def blupMatrix {n p q : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (X : Matrix n p ℝ) (Z : Matrix n q ℝ) (G : Matrix q q ℝ)
    (V : Matrix n n ℝ) : Matrix q n ℝ :=
  G * Zᵀ * V⁻¹ * (1 - X * glsMatrix X V)

/-- Mean-squared-error matrix of a linear predictor with weights `C`:
`C V Cᵀ - C Z G - G Zᵀ Cᵀ + G`, for `Cov u = G` and `Cov y = V`. -/
noncomputable def mseMatrix {n q : Type*} [Fintype n] [Fintype q]
    (Z : Matrix n q ℝ) (G : Matrix q q ℝ) (V : Matrix n n ℝ)
    (C : Matrix q n ℝ) : Matrix q q ℝ :=
  C * V * Cᵀ - C * Z * G - G * Zᵀ * Cᵀ + G

/-- In the linear model `y = X β + e`, the GLS estimate is `β + B e`. -/
theorem glsEstimator_add {n p : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hX : IsUnit (Xᵀ * V⁻¹ * X)) (β : p → ℝ) (e : n → ℝ) :
    glsEstimator X V (X *ᵥ β + e) = β + glsMatrix X V *ᵥ e := by
  change glsMatrix X V *ᵥ (X *ᵥ β + e) = β + glsMatrix X V *ᵥ e
  rw [mulVec_add, mulVec_mulVec, glsMatrix_mul_self hX, one_mulVec]

/-- Full column rank plus positive-definite noise make the GLS Gram matrix
invertible: `Xᵀ V⁻¹ X` is positive definite, hence a unit. -/
theorem isUnit_XtVinvX_of_linearIndependent {n p : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [DecidableEq p] (X : Matrix n p ℝ)
    (V : Matrix n n ℝ) (hV : V.PosDef)
    (hrank : LinearIndependent ℝ X.col) : IsUnit (Xᵀ * V⁻¹ * X) := by
  have hInj : Function.Injective X.mulVec := Matrix.mulVec_injective_iff.mpr hrank
  have hPD : (Xᵀ * V⁻¹ * X).PosDef := by
    have h := hV.inv.conjTranspose_mul_mul_same hInj
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact hPD.isUnit

private theorem memLp_glsMulVec_apply {n p : Type*} [Fintype n]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (A : Matrix p n ℝ)
    {ε : Ω → n → ℝ} {r : ENNReal} (hε : ∀ i, MemLp (fun ω => ε ω i) r μ)
    (a : p) : MemLp (fun ω => (A *ᵥ ε ω) a) r μ := by
  simp only [mulVec, dotProduct]
  exact memLp_finsetSum _ fun i _ => (hε i).const_mul _

/-- **Unbiasedness of GLS**, componentwise: with mean-zero errors, the GLS
estimator of `β` in `y = X β + ε` has expectation `β`. -/
theorem integral_glsEstimator_apply {n p : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hX : IsUnit (Xᵀ * V⁻¹ * X)) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (β : p → ℝ) {ε : Ω → n → ℝ}
    (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) (j : p) :
    ∫ ω, glsEstimator X V (X *ᵥ β + ε ω) j ∂μ = β j := by
  simp_rw [glsEstimator_add hX, Pi.add_apply, mulVec, dotProduct]
  rw [integral_add (integrable_const _)
      (integrable_finsetSum _ fun i _ => (hint i).const_mul _),
    integral_finsetSum _ fun i _ => (hint i).const_mul _]
  simp [integral_const_mul, hmean]

/-- **Unbiasedness of GLS**, vector form: `∫ β̂ dμ = β`. -/
theorem integral_glsEstimator {n p : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hX : IsUnit (Xᵀ * V⁻¹ * X)) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (β : p → ℝ) {ε : Ω → n → ℝ}
    (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
    ∫ ω, glsEstimator X V (X *ᵥ β + ε ω) ∂μ = β := by
  have hβ : ∀ j, Integrable (fun ω => glsEstimator X V (X *ᵥ β + ε ω) j) μ :=
    fun j => by
      simp_rw [glsEstimator_add hX, Pi.add_apply]
      exact (integrable_const _).add <| (memLp_glsMulVec_apply _
        (fun i => (memLp_one_iff_integrable).2 (hint i)) j).integrable le_rfl
  funext j
  rw [eval_integral hβ, integral_glsEstimator_apply hX β hint hmean]

/-- **Covariance of GLS**: with error covariance `V`, the GLS estimator has
`cov[β̂ a, β̂ b] = (Xᵀ V⁻¹ X)⁻¹ a b`. No mean-zero hypothesis is needed. -/
theorem covariance_glsEstimator {n p : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (β : p → ℝ)
    {ε : Ω → n → ℝ} (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = V i j)
    (a b : p) :
    cov[fun ω => glsEstimator X V (X *ᵥ β + ε ω) a,
      fun ω => glsEstimator X V (X *ᵥ β + ε ω) b; μ] =
      (Xᵀ * V⁻¹ * X)⁻¹ a b := by
  have hint : ∀ c, Integrable (fun ω => (glsMatrix X V *ᵥ ε ω) c) μ := fun c =>
    (memLp_glsMulVec_apply _ hL2 c).integrable (by norm_num)
  simp_rw [glsEstimator_add hX, Pi.add_apply]
  rw [covariance_const_add_left (hint a), covariance_const_add_right (hint b)]
  simp only [mulVec, dotProduct]
  rw [covariance_fun_sum_fun_sum (X := fun i ω => glsMatrix X V a i * ε ω i)
    (Y := fun j ω => glsMatrix X V b j * ε ω j) (fun i => (hL2 i).const_mul _)
    (fun j => (hL2 j).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
  have hexpand : (glsMatrix X V * V * (glsMatrix X V)ᵀ) a b =
      ∑ i, ∑ j, glsMatrix X V a i * (glsMatrix X V b j * V i j) := by
    have e1 : (glsMatrix X V * V * (glsMatrix X V)ᵀ) a b =
        ∑ k, ∑ i, glsMatrix X V a i * (V i k * glsMatrix X V b k) := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [← hexpand, glsMatrix_mul_mul_transpose hV hX]

/-- Mixed-model GLS unbiasedness: with `G : Matrix (Fin q) (Fin q)`,
`R V : Matrix (Fin n) (Fin n)` and `V = phenCov Z G R` the marginal
covariance, the GLS estimator at `V` is unbiased for `β`. -/
theorem mixed_glsEstimator_unbiased {n p q : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (Z : Matrix (Fin n) (Fin q) ℝ) (G : Matrix (Fin q) (Fin q) ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ)
    (hX : IsUnit (Xᵀ * (phenCov Z G R)⁻¹ * X)) {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (β : Fin p → ℝ) {ε : Ω → Fin n → ℝ}
    (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
    ∫ ω, glsEstimator X (phenCov Z G R) (X *ᵥ β + ε ω) ∂μ = β :=
  integral_glsEstimator hX β hint hmean

/-- Mixed-model GLS covariance: with the same `G`/`R`/`V` dimensions as above,
`cov[β̂ a, β̂ b] = (Xᵀ V⁻¹ X)⁻¹ a b` at `V = phenCov Z G R`. -/
theorem mixed_glsEstimator_covariance {n p q : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (Z : Matrix (Fin n) (Fin q) ℝ) (G : Matrix (Fin q) (Fin q) ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (hR : R.PosDef)
    (hX : IsUnit (Xᵀ * (phenCov Z G R)⁻¹ * X)) {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (β : Fin p → ℝ) {ε : Ω → Fin n → ℝ}
    (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] =
      phenCov Z G R i j) (a b : Fin p) :
    cov[fun ω => glsEstimator X (phenCov Z G R) (X *ᵥ β + ε ω) a,
      fun ω => glsEstimator X (phenCov Z G R) (X *ᵥ β + ε ω) b; μ] =
      (Xᵀ * (phenCov Z G R)⁻¹ * X)⁻¹ a b :=
  covariance_glsEstimator (posDef_phenCov hG hR) hX β hL2 hcov a b

/-- Henderson's equations carry the GLS estimator: `(b, u)` solves the MME
exactly when `b` is `glsEstimator` at `V = phenCov Z G R`. -/
theorem isMMESolution_iff_glsEstimator {n p q : ℕ}
    (X : Matrix (Fin n) (Fin p) ℝ) (Z : Matrix (Fin n) (Fin q) ℝ)
    (G : Matrix (Fin q) (Fin q) ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hR : R.PosDef)
    (hX : IsUnit (Xᵀ * (phenCov Z G R)⁻¹ * X)) (y : Fin n → ℝ)
    (b : Fin p → ℝ) (u : Fin q → ℝ) :
    IsMMESolution X Z G R y b u ↔
      b = glsEstimator X (phenCov Z G R) y ∧
        u = (G * Zᵀ * (phenCov Z G R)⁻¹) *ᵥ (y - X *ᵥ b) :=
  isMMESolution_iff_gls hG hR hX y b u

/-- Prediction weights annihilate the design: `L * X = 0`, in contrast with
the estimation identity `B * X = 1`. -/
theorem blupMatrix_mul_X {n p q : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {X : Matrix n p ℝ} {Z : Matrix n q ℝ} {G : Matrix q q ℝ}
    {V : Matrix n n ℝ} (hX : IsUnit (Xᵀ * V⁻¹ * X)) :
    blupMatrix X Z G V * X = 0 := by
  have h : (1 - X * glsMatrix X V) * X = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
      glsMatrix_mul_self hX, Matrix.mul_one, sub_self]
  change G * Zᵀ * V⁻¹ * (1 - X * glsMatrix X V) * X = 0
  rw [Matrix.mul_assoc, h, Matrix.mul_zero]

/-- The BLUP prediction error is free of the fixed effects: with
`L = blupMatrix`, `L (X β + Z u + e) - u = (L Z - 1) u + L e`. -/
theorem blupPredictionError_eq {n p q : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {X : Matrix n p ℝ} {Z : Matrix n q ℝ} {G : Matrix q q ℝ}
    {V : Matrix n n ℝ} (hX : IsUnit (Xᵀ * V⁻¹ * X)) (β : p → ℝ)
    (u : q → ℝ) (e : n → ℝ) :
    blupMatrix X Z G V *ᵥ (X *ᵥ β + Z *ᵥ u + e) - u =
      (blupMatrix X Z G V * Z - 1) *ᵥ u + blupMatrix X Z G V *ᵥ e := by
  have hLX : blupMatrix X Z G V * X = 0 := blupMatrix_mul_X hX
  rw [mulVec_add, mulVec_add, mulVec_mulVec, mulVec_mulVec, hLX,
    zero_mulVec, zero_add, Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

/-- **BLUP MSE-matrix minimality**, the prediction analogue of Aitken's
theorem: for positive-definite `G` and `V`, among all weight matrices `C`
with `C * X = 0`, the BLUP weights minimize
`C ↦ C V Cᵀ - C Z G - G Zᵀ Cᵀ + G` in the positive-semidefinite order. -/
theorem blup_mse_minimality {n p q : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {X : Matrix n p ℝ} {Z : Matrix n q ℝ} {G : Matrix q q ℝ}
    {V : Matrix n n ℝ} (hG : G.PosDef) (hV : V.PosDef)
    (hX : IsUnit (Xᵀ * V⁻¹ * X)) (C : Matrix q n ℝ) (hC : C * X = 0) :
    (mseMatrix Z G V C -
      mseMatrix Z G V (blupMatrix X Z G V)).PosSemidef := by
  set L := blupMatrix X Z G V with hL
  have hGt : Gᵀ = G := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.eq
  have hVt : Vᵀ = V := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hV.isHermitian.eq
  have hVit : (V⁻¹)ᵀ = V⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hVt]
  have hW : ((Xᵀ * V⁻¹ * X)⁻¹)ᵀ = (Xᵀ * V⁻¹ * X)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hVit, Matrix.mul_assoc]
  have hB : (glsMatrix X V)ᵀ * Xᵀ * V⁻¹ = V⁻¹ * X * glsMatrix X V := by
    change ((Xᵀ * V⁻¹ * X)⁻¹ * Xᵀ * V⁻¹)ᵀ * Xᵀ * V⁻¹
      = V⁻¹ * X * ((Xᵀ * V⁻¹ * X)⁻¹ * Xᵀ * V⁻¹)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hVit, hW]
    simp only [Matrix.mul_assoc]
  have hGZ : (G * Zᵀ)ᵀ = Z * G := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hGt]
  have h1XB : (1 - X * glsMatrix X V)ᵀ = 1 - (glsMatrix X V)ᵀ * Xᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
  have hV1 : V * (1 - (glsMatrix X V)ᵀ * Xᵀ) * V⁻¹
      = 1 - X * glsMatrix X V := by
    have hVi : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    rw [show V * ((glsMatrix X V)ᵀ * Xᵀ) * V⁻¹
        = V * (V⁻¹ * X * glsMatrix X V) from by
      rw [Matrix.mul_assoc, hB]]
    rw [← Matrix.mul_assoc V (V⁻¹ * X), ← Matrix.mul_assoc V V⁻¹,
      Matrix.mul_nonsing_inv _ hVi, Matrix.one_mul]
  have hVL : V * Lᵀ = Z * G - X * (glsMatrix X V * (Z * G)) := by
    rw [hL]
    unfold blupMatrix
    rw [Matrix.transpose_mul, Matrix.transpose_mul, h1XB, hVit, hGZ,
      ← Matrix.mul_assoc V _ _, ← Matrix.mul_assoc (V * _) _ _, hV1,
      Matrix.sub_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  have hLX : L * X = 0 := blupMatrix_mul_X hX
  have hDX : (C - L) * X = 0 := by
    rw [Matrix.sub_mul, hC, hLX, sub_self]
  have h1 : (C - L) * V * Lᵀ = (C - L) * (Z * G) := by
    rw [Matrix.mul_assoc, hVL, Matrix.mul_sub,
      show (C - L) * (X * (glsMatrix X V * (Z * G))) = 0 from by
        rw [← Matrix.mul_assoc, hDX, Matrix.zero_mul],
      sub_zero]
  have h1t : L * V * (C - L)ᵀ = G * Zᵀ * (C - L)ᵀ := by
    have h := congrArg Matrix.transpose h1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hVt,
      hGt] at h
    rwa [← Matrix.mul_assoc] at h
  have key : mseMatrix Z G V C - mseMatrix Z G V L
      = (C - L) * V * (C - L)ᵀ := by
    have hC' : C = (C - L) + L := (sub_add_cancel C L).symm
    have e1 : C * V * Cᵀ = ((C - L) + L) * V * ((C - L) + L)ᵀ := by
      rw [← hC']
    have e2 : C * Z * G = ((C - L) + L) * Z * G := by rw [← hC']
    have e3 : G * Zᵀ * Cᵀ = G * Zᵀ * ((C - L) + L)ᵀ := by rw [← hC']
    unfold mseMatrix
    rw [e1, e2, e3]
    simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    rw [h1, h1t]
    simp only [Matrix.mul_assoc]
    abel
  rw [key]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hV.posSemidef.mul_mul_conjTranspose_same (C - L)

end MathlibExt.Probability.Statistics.GeneralizedLeastSquaresBridge
