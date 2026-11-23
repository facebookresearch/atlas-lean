/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Code.ChapterII.CovarianceMatrix
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# CDIS Probabilités IV: characteristic function of a Gaussian vector

* id 89: a random vector `X` of `ℝⁿ` is Gaussian iff its characteristic function is
  `φ_X(u) = exp(i ⟨u, m⟩ - ⟨u, C u⟩ / 2)` for some `m ∈ ℝⁿ` and some positive semidefinite
  matrix `C`; then `m = E(X)` and `C` is the covariance matrix of `X`.

The statements are about the law `μ` of `X` on `EuclideanSpace ℝ ι`. No moment hypothesis is
assumed: as in the course, the finite second moment, the mean and the covariance follow from
the form of `φ_X`, through Mathlib's `multivariateGaussian m C` and the injectivity of the
characteristic function. Mean and covariance are the id 39 objects `meanVector` and
`covMatrix` of the coordinates.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

namespace CDIS

variable {ι : Type*} [Fintype ι] {μ : Measure (EuclideanSpace ℝ ι)}

/-- The coordinates of a square-integrable random vector are square integrable. -/
lemma memLp_two_coord_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → EuclideanSpace ℝ ι} (h2 : MemLp X 2 P) (i : ι) : MemLp (fun ω ↦ X ω i) 2 P :=
  (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ ι)).comp_memLp' h2

/-- The coordinates of a square-integrable law are square integrable. -/
lemma memLp_two_coord (h2 : MemLp id 2 μ) (i : ι) :
    MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ :=
  memLp_two_coord_comp h2 i

/-- The inner product of `ℝⁿ` in coordinates. -/
lemma inner_eq_sum_mul (u x : EuclideanSpace ℝ ι) : ⟪u, x⟫ = ∑ i, u i * x i := by
  simp [PiLp.inner_apply, mul_comm]

/-- The covariance bilinear form of Mathlib is the quadratic form of the covariance matrix of
id 39: `Var(⟨u, X⟩) = ⟨u, C u⟩`. -/
theorem covarianceBilin_self_eq_covMatrix [IsProbabilityMeasure μ] (h2 : MemLp id 2 μ)
    (u : EuclideanSpace ℝ ι) :
    covarianceBilin μ u u = u ⬝ᵥ covMatrix (fun i (x : EuclideanSpace ℝ ι) ↦ x i) μ *ᵥ u := by
  rw [covarianceBilin_self h2, dotProduct_covMatrix_mulVec (memLp_two_coord h2)]
  simp_rw [inner_eq_sum_mul]

/-- The mean vector of id 39 is the coordinate vector of the Bochner mean. -/
lemma meanVector_coord (hint : Integrable id μ) :
    meanVector (fun i (x : EuclideanSpace ℝ ι) ↦ x i) μ = fun i ↦ (∫ x, x ∂μ) i := by
  funext i
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hint

/-- CDIS P.IV, id 89, direct part: a Gaussian vector has characteristic function
`exp(i ⟨u, m⟩ - ⟨u, C u⟩ / 2)` with `m = E(X)` and `C` its covariance matrix. -/
theorem charFun_eq_of_isGaussian [IsGaussian μ] (u : EuclideanSpace ℝ ι) :
    charFun μ u = Complex.exp (⟪u, ∫ x, x ∂μ⟫ * Complex.I -
      u ⬝ᵥ covMatrix (fun i (x : EuclideanSpace ℝ ι) ↦ x i) μ *ᵥ u / 2) := by
  rw [IsGaussian.charFun_eq', covarianceBilin_self_eq_covMatrix IsGaussian.memLp_two_id]
  rfl

variable [DecidableEq ι]

/-- A law whose characteristic function has the Gaussian form, with `C` positive semidefinite,
is Mathlib's `multivariateGaussian m C`. -/
theorem eq_multivariateGaussian_of_charFun_eq [IsProbabilityMeasure μ]
    {m : EuclideanSpace ℝ ι} {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (h : ∀ u, charFun μ u = Complex.exp (⟪u, m⟫ * Complex.I - u ⬝ᵥ C *ᵥ u / 2)) :
    μ = multivariateGaussian m C :=
  Measure.ext_of_charFun (funext fun u ↦ by rw [h, charFun_multivariateGaussian hC])

omit [DecidableEq ι] in
/-- CDIS P.IV, id 89: `X` is a Gaussian vector iff its characteristic function is
`exp(i ⟨u, m⟩ - ⟨u, C u⟩ / 2)` for some `m` and some positive semidefinite `C`. -/
theorem isGaussian_iff_exists_charFun_eq [IsProbabilityMeasure μ] :
    IsGaussian μ ↔ ∃ (m : EuclideanSpace ℝ ι) (C : Matrix ι ι ℝ), C.PosSemidef ∧
      ∀ u, charFun μ u = Complex.exp (⟪u, m⟫ * Complex.I - u ⬝ᵥ C *ᵥ u / 2) := by
  classical
  refine ⟨fun _ ↦ ⟨_, _, covMatrix_posSemidef (memLp_two_coord IsGaussian.memLp_two_id),
    charFun_eq_of_isGaussian⟩, ?_⟩
  rintro ⟨m, C, hC, h⟩
  rw [eq_multivariateGaussian_of_charFun_eq hC h]
  infer_instance

omit [DecidableEq ι] in
/-- CDIS P.IV, id 89, identification: when the characteristic function has the Gaussian form,
`m` is the mean vector and `C` the covariance matrix of `X`. -/
theorem mean_covMatrix_of_charFun_eq [IsProbabilityMeasure μ]
    {m : EuclideanSpace ℝ ι} {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (h : ∀ u, charFun μ u = Complex.exp (⟪u, m⟫ * Complex.I - u ⬝ᵥ C *ᵥ u / 2)) :
    meanVector (fun i (x : EuclideanSpace ℝ ι) ↦ x i) μ = (fun i ↦ m i) ∧
      covMatrix (fun i (x : EuclideanSpace ℝ ι) ↦ x i) μ = C := by
  classical
  rw [eq_multivariateGaussian_of_charFun_eq hC h, meanVector_coord IsGaussian.integrable_id,
    integral_id_multivariateGaussian]
  refine ⟨rfl, ?_⟩
  ext i j
  exact covariance_eval_multivariateGaussian hC i j

end CDIS
