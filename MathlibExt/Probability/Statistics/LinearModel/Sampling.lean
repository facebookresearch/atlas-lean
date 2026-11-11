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
No Gaussianity is assumed, and no `t` or `F` sampling law is derived here. Rank-deficient designs
are excluded by the hypothesis `IsUnit (Xᵀ * X)`.

## Main results

* `olsMatrix`, `olsMatrix_eq`: the OLS matrix `(Xᵀ X)⁻¹ Xᵀ`, defined as `glsMatrix X 1`.
* `olsEstimator`, `olsEstimator_add`: `β̂ (X β + e) = β + B e`.
* `integral_olsEstimator_apply`, `integral_olsEstimator`: unbiasedness.
* `covariance_olsEstimator`: `Cov(β̂ a, β̂ b) = σ² ((Xᵀ X)⁻¹) a b`.
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

end MathlibExt.Probability.Statistics.LinearModel
