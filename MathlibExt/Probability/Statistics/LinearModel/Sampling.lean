/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import MathlibExt.Probability.Distributions.CochranTheorem

/-!
# Sampling properties of the ordinary least-squares estimator

For a design matrix `X : Matrix m k ℝ` with invertible Gram matrix `Xᵀ X`, the ordinary
least-squares (OLS) matrix is `B = (Xᵀ X)⁻¹ Xᵀ`, the generalized least-squares matrix of
`MathlibExt.Probability.Statistics.GeneralizedLeastSquares` at noise covariance `V = 1`. In the
linear model `y = X β + ε` the OLS estimator `β̂ = B y` satisfies `β̂ = β + B ε`, so

* `β̂` is unbiased when the errors have mean zero: `𝔼[β̂ j] = β j`;
* `Cov(β̂ a, β̂ b) = σ² ((Xᵀ X)⁻¹) a b` when the errors are square-integrable, uncorrelated and of
  common variance `σ²`.

These are moment results: they hold for any error law with the stated first and second moments.
No Gaussianity is assumed for them. Rank-deficient designs are excluded by the hypothesis
`IsUnit (Xᵀ * X)`.

For i.i.d. normal errors, the residual-maker matrix `M = 1 - X B` is a symmetric idempotent of
rank `n - p` (`n = card m`, `p = card k`), so Cochran's theorem gives
`‖y - X β̂‖² / σ² ~ χ²_{n-p}` when `p < n`. Not covered here: independence of `β̂` and the
residuals, and the Student `t` and Snedecor `F` laws built from them.

## Main results

* `olsMatrix`, `olsMatrix_eq`: the OLS matrix `(Xᵀ X)⁻¹ Xᵀ`, defined as `glsMatrix X 1`.
* `olsEstimator`, `olsEstimator_add`: `β̂ (X β + e) = β + B e`.
* `integral_olsEstimator_apply`, `integral_olsEstimator`: unbiasedness.
* `covariance_olsEstimator`: `Cov(β̂ a, β̂ b) = σ² ((Xᵀ X)⁻¹) a b`.
* `residualMatrix`: `M = 1 - X (Xᵀ X)⁻¹ Xᵀ`; `residualMatrix_isHermitian`,
  `residualMatrix_mul_self`, `residualMatrix_mul`, `sub_mulVec_olsEstimator`,
  `rank_residualMatrix` (`rank M = n - p`).
* `hasLaw_rss`, `hasLaw_rss_div_sq`: `‖y - X β̂‖² / σ² ~ χ²_{n-p}` for normal errors.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares

namespace MathlibExt.Probability.Statistics.LinearModel

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- The ordinary least-squares matrix, the generalized least-squares matrix `glsMatrix X V` at
noise covariance `V = 1`; it equals `(Xᵀ X)⁻¹ Xᵀ` (`olsMatrix_eq`). -/
noncomputable def olsMatrix (X : Matrix m k ℝ) : Matrix k m ℝ :=
  glsMatrix X 1

@[simp]
theorem olsMatrix_eq (X : Matrix m k ℝ) : olsMatrix X = (Xᵀ * X)⁻¹ * Xᵀ := by
  rw [olsMatrix, glsMatrix, inv_one, Matrix.mul_one, Matrix.mul_one]

/-- The ordinary least-squares estimate `(Xᵀ X)⁻¹ Xᵀ y` of `β` in `y = X β + ε`. -/
noncomputable def olsEstimator (X : Matrix m k ℝ) (y : m → ℝ) : k → ℝ :=
  olsMatrix X *ᵥ y

variable {X : Matrix m k ℝ}

/-- The `V = 1` instance of the GLS invertibility hypothesis `IsUnit (Xᵀ * V⁻¹ * X)`. -/
private theorem isUnit_gram_inv_one (hX : IsUnit (Xᵀ * X)) :
    IsUnit (Xᵀ * (1 : Matrix m m ℝ)⁻¹ * X) := by
  rwa [inv_one, Matrix.mul_one]

/-- `B X = 1` for the OLS matrix `B`, from `glsMatrix_mul_self` at `V = 1`. -/
theorem olsMatrix_mul_self (hX : IsUnit (Xᵀ * X)) : olsMatrix X * X = 1 :=
  glsMatrix_mul_self (isUnit_gram_inv_one hX)

/-- `B Bᵀ = (Xᵀ X)⁻¹` for the OLS matrix `B`, from `glsMatrix_mul_mul_transpose` at `V = 1`. -/
theorem olsMatrix_mul_transpose (hX : IsUnit (Xᵀ * X)) :
    olsMatrix X * (olsMatrix X)ᵀ = (Xᵀ * X)⁻¹ := by
  have h := glsMatrix_mul_mul_transpose (X := X) Matrix.PosDef.one (isUnit_gram_inv_one hX)
  rwa [Matrix.mul_one, inv_one, Matrix.mul_one] at h

/-- In the linear model `y = X β + e`, the OLS estimate is `β + B e`. -/
theorem olsEstimator_add (hX : IsUnit (Xᵀ * X)) (β : k → ℝ) (e : m → ℝ) :
    olsEstimator X (X *ᵥ β + e) = β + olsMatrix X *ᵥ e := by
  rw [olsEstimator, mulVec_add, mulVec_mulVec, olsMatrix_mul_self hX, one_mulVec]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [DecidableEq m] [Fintype k] [DecidableEq k] in
private theorem memLp_mulVec_apply {p : ENNReal} (A : Matrix k m ℝ) {ε : Ω → m → ℝ}
    (hε : ∀ i, MemLp (fun ω => ε ω i) p μ) (a : k) :
    MemLp (fun ω => (A *ᵥ ε ω) a) p μ := by
  simp only [mulVec, dotProduct]
  exact memLp_finsetSum _ fun i _ => (hε i).const_mul _

/-- **Unbiasedness of OLS**, componentwise: if the errors are integrable with mean zero, the
OLS estimator of `β` in `y = X β + ε` has expectation `β`. -/
theorem integral_olsEstimator_apply [IsProbabilityMeasure μ] (hX : IsUnit (Xᵀ * X))
    (β : k → ℝ) {ε : Ω → m → ℝ} (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) (j : k) :
    ∫ ω, olsEstimator X (X *ᵥ β + ε ω) j ∂μ = β j := by
  simp_rw [olsEstimator_add hX, Pi.add_apply, mulVec, dotProduct]
  rw [integral_add (integrable_const _)
      (integrable_finsetSum _ fun i _ => (hint i).const_mul _),
    integral_finsetSum _ fun i _ => (hint i).const_mul _]
  simp [integral_const_mul, hmean]

/-- **Unbiasedness of OLS**, vector form: `∫ β̂ dμ = β`. -/
theorem integral_olsEstimator [IsProbabilityMeasure μ] (hX : IsUnit (Xᵀ * X))
    (β : k → ℝ) {ε : Ω → m → ℝ} (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
    ∫ ω, olsEstimator X (X *ᵥ β + ε ω) ∂μ = β := by
  have hβ : ∀ j, Integrable (fun ω => olsEstimator X (X *ᵥ β + ε ω) j) μ := fun j => by
    simp_rw [olsEstimator_add hX, Pi.add_apply]
    exact (integrable_const _).add <| (memLp_mulVec_apply _
      (fun i => (memLp_one_iff_integrable).2 (hint i)) j).integrable le_rfl
  funext j
  rw [eval_integral hβ, integral_olsEstimator_apply hX β hint hmean]

/-- **Covariance of OLS**: if the errors are square-integrable, pairwise uncorrelated and of
common variance `σ²`, i.e. `cov[ε i, ε j; μ] = if i = j then σ ^ 2 else 0`, then
`cov[β̂ a, β̂ b; μ] = σ² ((Xᵀ X)⁻¹) a b`. No mean-zero or Gaussian hypothesis is needed. -/
theorem covariance_olsEstimator [IsProbabilityMeasure μ] (hX : IsUnit (Xᵀ * X))
    (β : k → ℝ) {ε : Ω → m → ℝ} (σ : ℝ) (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = if i = j then σ ^ 2 else 0)
    (a b : k) :
    cov[fun ω => olsEstimator X (X *ᵥ β + ε ω) a,
      fun ω => olsEstimator X (X *ᵥ β + ε ω) b; μ] = σ ^ 2 * (Xᵀ * X)⁻¹ a b := by
  have hint : ∀ c, Integrable (fun ω => (olsMatrix X *ᵥ ε ω) c) μ := fun c =>
    (memLp_mulVec_apply _ hL2 c).integrable (by norm_num)
  simp_rw [olsEstimator_add hX, Pi.add_apply]
  rw [covariance_const_add_left (hint a), covariance_const_add_right (hint b)]
  simp only [mulVec, dotProduct]
  rw [covariance_fun_sum_fun_sum (X := fun i ω => olsMatrix X a i * ε ω i)
    (Y := fun j ω => olsMatrix X b j * ε ω j) (fun i => (hL2 i).const_mul _)
    (fun j => (hL2 j).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
  rw [← olsMatrix_mul_transpose hX, Matrix.mul_apply, Finset.mul_sum]
  simp only [transpose_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### Residuals and the Gaussian residual sum of squares -/

/-- The residual-maker matrix `1 - X (Xᵀ X)⁻¹ Xᵀ`: `residualMatrix X *ᵥ y = y - X β̂`
(`sub_mulVec_olsEstimator`). -/
noncomputable def residualMatrix (X : Matrix m k ℝ) : Matrix m m ℝ :=
  1 - X * olsMatrix X

omit [DecidableEq m] in
private theorem transpose_gram_inv (X : Matrix m k ℝ) : ((Xᵀ * X)⁻¹)ᵀ = (Xᵀ * X)⁻¹ := by
  rw [transpose_nonsing_inv, transpose_mul, transpose_transpose]

/-- The residual-maker matrix is symmetric. -/
theorem residualMatrix_transpose (X : Matrix m k ℝ) : (residualMatrix X)ᵀ = residualMatrix X := by
  rw [residualMatrix, transpose_sub, transpose_one, transpose_mul, olsMatrix_eq, transpose_mul,
    transpose_transpose, transpose_gram_inv, Matrix.mul_assoc]

theorem residualMatrix_isHermitian (X : Matrix m k ℝ) : (residualMatrix X).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, residualMatrix_transpose]

theorem residualMatrix_mul (hX : IsUnit (Xᵀ * X)) : residualMatrix X * X = 0 := by
  rw [residualMatrix, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, olsMatrix_mul_self hX,
    Matrix.mul_one, sub_self]

private theorem olsMatrix_mul_residualMatrix (hX : IsUnit (Xᵀ * X)) :
    olsMatrix X * residualMatrix X = 0 := by
  rw [residualMatrix, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, olsMatrix_mul_self hX,
    Matrix.one_mul, sub_self]

/-- The residual-maker matrix is idempotent. -/
theorem residualMatrix_mul_self (hX : IsUnit (Xᵀ * X)) :
    residualMatrix X * residualMatrix X = residualMatrix X := by
  conv_lhs => arg 1; rw [residualMatrix]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, olsMatrix_mul_residualMatrix hX,
    Matrix.mul_zero, sub_zero]

/-- The OLS residuals `y - X β̂` are `residualMatrix X *ᵥ y`. -/
theorem sub_mulVec_olsEstimator (X : Matrix m k ℝ) (y : m → ℝ) :
    y - X *ᵥ olsEstimator X y = residualMatrix X *ᵥ y := by
  rw [residualMatrix, sub_mulVec, one_mulVec, olsEstimator, mulVec_mulVec]

/-- In `y = X β + e` the residuals depend only on the errors: `residualMatrix X *ᵥ e`. -/
theorem residualMatrix_mulVec_add (hX : IsUnit (Xᵀ * X)) (β : k → ℝ) (e : m → ℝ) :
    residualMatrix X *ᵥ (X *ᵥ β + e) = residualMatrix X *ᵥ e := by
  rw [mulVec_add, mulVec_mulVec, residualMatrix_mul hX, zero_mulVec, zero_add]

/-- The residual sum of squares in `y = X β + e` is the quadratic form `eᵀ M e` of the
residual-maker matrix `M`. -/
theorem rss_eq_dotProduct_residualMatrix (hX : IsUnit (Xᵀ * X)) (β : k → ℝ) (e : m → ℝ) :
    (X *ᵥ β + e - X *ᵥ olsEstimator X (X *ᵥ β + e)) ⬝ᵥ
        (X *ᵥ β + e - X *ᵥ olsEstimator X (X *ᵥ β + e)) =
      e ⬝ᵥ residualMatrix X *ᵥ e := by
  rw [sub_mulVec_olsEstimator, residualMatrix_mulVec_add hX, dotProduct_mulVec,
    ← residualMatrix_transpose X, vecMul_transpose, mulVec_mulVec, residualMatrix_transpose,
    residualMatrix_mul_self hX, dotProduct_comm]

/-- Rank equals trace for an idempotent real matrix, from `IsProj.trace`. -/
private theorem rank_eq_trace_of_mul_self {n : Type*} [Fintype n]
    {A : Matrix n n ℝ} (hA : A * A = A) : (A.rank : ℝ) = A.trace := by
  classical
  have hidem : IsIdempotentElem A.mulVecLin := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hA]
  rw [Matrix.rank, ← (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace,
    ← Matrix.trace_toLin'_eq]
  rfl

theorem trace_residualMatrix (hX : IsUnit (Xᵀ * X)) :
    (residualMatrix X).trace = Fintype.card m - Fintype.card k := by
  rw [residualMatrix, trace_sub, trace_one, trace_mul_comm, olsMatrix_mul_self hX, trace_one]

/-- The residual-maker matrix has rank `n - p` for a full-rank `n × p` design. -/
theorem rank_residualMatrix (hX : IsUnit (Xᵀ * X)) :
    (residualMatrix X).rank = Fintype.card m - Fintype.card k := by
  have h := rank_eq_trace_of_mul_self (residualMatrix_mul_self hX)
  rw [trace_residualMatrix hX] at h
  have h' : (residualMatrix X).rank + Fintype.card k = Fintype.card m := by
    exact_mod_cast (by linarith : ((residualMatrix X).rank : ℝ) + Fintype.card k = Fintype.card m)
  omega

/-- **Gaussian residual quadratic form**: if the errors are i.i.d. standard normal and
`p < n`, the quadratic form `εᵀ M ε` of the residual-maker matrix is `χ²_{n-p}`. -/
theorem hasLaw_dotProduct_residualMatrix (hX : IsUnit (Xᵀ * X))
    (hkm : Fintype.card k < Fintype.card m) {ε : Ω → m → ℝ}
    (hε : HasLaw ε (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    HasLaw (fun ω => ε ω ⬝ᵥ residualMatrix X *ᵥ ε ω)
      (chiSquareMeasure (Fintype.card m - Fintype.card k)) μ := by
  have hr : 0 < (residualMatrix X).rank := by rw [rank_residualMatrix hX]; omega
  refine HasLaw.fun_comp (Y := fun x => x ⬝ᵥ residualMatrix X *ᵥ x) ⟨by fun_prop, ?_⟩ hε
  rw [pi_gaussianReal_map_dotProduct_mulVec (residualMatrix_isHermitian X)
    (residualMatrix_mul_self hX) hr, rank_residualMatrix hX]

/-- **Law of the residual sum of squares**, `σ = 1`: in `y = X β + ε` with i.i.d. standard normal
errors and `p < n`, `‖y - X β̂‖² ~ χ²_{n-p}`. -/
theorem hasLaw_rss (hX : IsUnit (Xᵀ * X)) (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {ε : Ω → m → ℝ} (hε : HasLaw ε (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    HasLaw (fun ω => (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
        (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)))
      (chiSquareMeasure (Fintype.card m - Fintype.card k)) μ := by
  simp_rw [rss_eq_dotProduct_residualMatrix hX]
  exact hasLaw_dotProduct_residualMatrix hX hkm hε

/-- **Law of the residual sum of squares**, general scale: if the standardised errors `σ⁻¹ ε`
are i.i.d. standard normal and `p < n`, then `‖y - X β̂‖² / σ² ~ χ²_{n-p}`. -/
theorem hasLaw_rss_div_sq (hX : IsUnit (Xᵀ * X)) (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {ε : Ω → m → ℝ} (σ : ℝ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    HasLaw (fun ω => (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
        (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) / σ ^ 2)
      (chiSquareMeasure (Fintype.card m - Fintype.card k)) μ := by
  convert hasLaw_dotProduct_residualMatrix hX hkm hε using 2 with ω
  rw [rss_eq_dotProduct_residualMatrix hX, mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  ring

end MathlibExt.Probability.Statistics.LinearModel
