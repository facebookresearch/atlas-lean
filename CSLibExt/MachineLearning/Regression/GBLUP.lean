/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GaussianProcessRegression
public import CSLibExt.MachineLearning.Regression.LeastSquares
public import MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem

/-!
# RR-BLUP = GBLUP = kernel ridge regression = Gaussian-process posterior mean

Genomic prediction regresses phenotypes `y : Fin m → ℝ` of `m` individuals on their marker
genotypes, the rows of `Z : Matrix (Fin m) ι ℝ` (one column per marker). Two classical
predictors are:

* **RR-BLUP** (ridge-regression BLUP of marker effects; Meuwissen, Hayes and Goddard 2001):
  marker effects `β̂ = (ZᵀZ + λI)⁻¹ Zᵀ y` (`LeastSquares.ridgeEstimate Z y λ`) and predicted
  genetic values `Z' β̂` for any genotype matrix `Z'`;
* **GBLUP** (BLUP of genetic values with a genomic relationship matrix; VanRaden 2008): genetic
  values `Z' Zᵀ (ZZᵀ + λI)⁻¹ y`, with relationship (kernel) matrix `ZZᵀ`.

This file proves that they coincide, and that both are the posterior mean of Gaussian-process
regression with the linear marker kernel and the kernel ridge fit in any RKHS whose kernel has
Gram matrix `ZZᵀ` at the training individuals.

## Main results

* `transpose_mul_add_inv_mul_transpose`: the **push-through identity**
  `(ZᵀZ + λI)⁻¹ Zᵀ = Zᵀ (ZZᵀ + λI)⁻¹` for `λ > 0`.
* `mul_ridgeHat_eq_gblupHat`: `Z (ZᵀZ + λI)⁻¹ Zᵀ = ZZᵀ (ZZᵀ + λI)⁻¹` (RR-BLUP and GBLUP give
  the same fitted values); `mulVec_ridgeEstimate`: `Z' β̂ = Z' Zᵀ (ZZᵀ + λI)⁻¹ y` for any
  genotypes `Z'` (the same predictions for new individuals).
* `markerKernel s a b = s ⟪a, b⟫` and `gpMean_markerKernel`: the GP predictive-mean matrix for
  kernel `s ⟪a, b⟫` and noise variance `σ²` equals `Z' Zᵀ (ZZᵀ + (σ²/s) I)⁻¹`, i.e. GBLUP with
  `λ = σ²/s` (the ratio of residual to marker-effect variance).
* `condDistrib_markerKernel`: the GP posterior (`condDistrib_test_given_targets`) with the marker
  kernel has mean `Z' Zᵀ (ZZᵀ + (σ²/s) I)⁻¹ y = Z' β̂`.
* `kernelRidgeFit_eq_mulVec_ridgeEstimate`: the kernel ridge fit of the representer theorem, in
  any real RKHS whose Gram matrix at the training inputs is `ZZᵀ`, has fitted values `Z β̂`.

## Scope

The model has no fixed effects (Henderson's mixed-model equations with the random genetic effect
only). `Z` is any real genotype matrix, for instance VanRaden's centered matrix; GBLUP with
`G = ZZᵀ / c` and genetic variance `σ²_g` is the marker kernel with `s = σ²_g / c`, so the scaling
only changes `λ = σ²/s`. The Gaussian joint law of genetic values and phenotypes is a hypothesis,
as in `GaussianProcessRegression.lean`; no measure on marker effects is constructed.

## References

* C. R. Henderson, "Best linear unbiased estimation and prediction under a selection model",
  *Biometrics* **31** (1975), 423–447.
* T. H. E. Meuwissen, B. J. Hayes and M. E. Goddard, "Prediction of total genetic value using
  genome-wide dense marker maps", *Genetics* **157** (2001), 1819–1829.
* P. M. VanRaden, "Efficient methods to compute genomic predictions", *J. Dairy Sci.* **91**
  (2008), 4414–4423.
* J. B. Endelman, "Ridge regression and other kernels for genomic selection with R package
  rrBLUP", *Plant Genome* **4** (2011), 250–255.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.GBLUP

open Matrix MeasureTheory ProbabilityTheory WithLp
open Cslib.MachineLearning.LeastSquares Cslib.MachineLearning.GaussianProcessRegression

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

omit [DecidableEq ι] in
/-- For `λ > 0` the GBLUP matrix `ZZᵀ + λI` is positive definite. -/
theorem posDef_mul_transpose_add (Z : Matrix (Fin m) ι ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (Z * Zᵀ + lam • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef := by
  have h1 : (Z * Zᵀ).PosSemidef := by
    have := posSemidef_self_mul_conjTranspose Z
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  exact PosDef.posSemidef_add h1 (PosDef.one.smul hlam)

/-- The **push-through identity** `(ZᵀZ + λI)⁻¹ Zᵀ = Zᵀ (ZZᵀ + λI)⁻¹` for `λ > 0`. -/
theorem transpose_mul_add_inv_mul_transpose (Z : Matrix (Fin m) ι ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (Zᵀ * Z + lam • (1 : Matrix ι ι ℝ))⁻¹ * Zᵀ =
      Zᵀ * (Z * Zᵀ + lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ := by
  set A := Zᵀ * Z + lam • (1 : Matrix ι ι ℝ)
  set B := Z * Zᵀ + lam • (1 : Matrix (Fin m) (Fin m) ℝ)
  have hA : IsUnit A.det := (posDef_ridge Z hlam).det_pos.ne'.isUnit
  have hB : IsUnit B.det := (posDef_mul_transpose_add Z hlam).det_pos.ne'.isUnit
  have hAB : Zᵀ * B = A * Zᵀ := by
    simp only [A, B, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  calc A⁻¹ * Zᵀ = A⁻¹ * Zᵀ * (B * B⁻¹) := by rw [mul_nonsing_inv B hB, Matrix.mul_one]
    _ = A⁻¹ * (Zᵀ * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = A⁻¹ * A * Zᵀ * B⁻¹ := by rw [hAB]; simp only [Matrix.mul_assoc]
    _ = Zᵀ * B⁻¹ := by rw [nonsing_inv_mul A hA, Matrix.one_mul]

/-- **RR-BLUP = GBLUP** (fitted values): `Z (ZᵀZ + λI)⁻¹ Zᵀ = ZZᵀ (ZZᵀ + λI)⁻¹` for `λ > 0`. -/
theorem mul_ridgeHat_eq_gblupHat (Z : Matrix (Fin m) ι ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Z * (Zᵀ * Z + lam • (1 : Matrix ι ι ℝ))⁻¹ * Zᵀ =
      Z * Zᵀ * (Z * Zᵀ + lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ := by
  rw [Matrix.mul_assoc, transpose_mul_add_inv_mul_transpose Z hlam, Matrix.mul_assoc]

/-- The ridge marker effects are back-solved from GBLUP:
`(ZᵀZ + λI)⁻¹ Zᵀ y = Zᵀ (ZZᵀ + λI)⁻¹ y`. -/
theorem ridgeEstimate_eq (Z : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ridgeEstimate Z y lam =
      Zᵀ *ᵥ ((Z * Zᵀ + lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *ᵥ y) := by
  rw [ridgeEstimate, mulVec_mulVec, transpose_mul_add_inv_mul_transpose Z hlam, mulVec_mulVec]

/-- **RR-BLUP = GBLUP** (predictions): for any genotypes `Z'` (training or new individuals),
`Z' β̂ = Z' Zᵀ (ZZᵀ + λI)⁻¹ y`. -/
theorem mulVec_ridgeEstimate {τ : Type*} (Z' : Matrix τ ι ℝ)
    (Z : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Z' *ᵥ ridgeEstimate Z y lam =
      (Z' * Zᵀ * (Z * Zᵀ + lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹) *ᵥ y := by
  rw [ridgeEstimate_eq Z y hlam, mulVec_mulVec, mulVec_mulVec]

/-! ### The Gaussian-process view -/

/-- The linear marker kernel `k(a, b) = s ⟪a, b⟫ = s ∑ⱼ aⱼ bⱼ` on genotype vectors: the
covariance of genetic values `aᵀβ` and `bᵀβ` when the marker effects `β` are independent with
variance `s`. -/
noncomputable def markerKernel (s : ℝ) (a b : ι → ℝ) : ℝ :=
  s * (a ⬝ᵥ b)

omit [DecidableEq ι] in
/-- Unfolding `markerKernel`. -/
theorem markerKernel_apply (s : ℝ) (a b : ι → ℝ) : markerKernel s a b = s * (a ⬝ᵥ b) := rfl

omit [DecidableEq ι] in
/-- The kernel matrix of the marker kernel between genotypes `Z'` and `Z` is `s Z' Zᵀ`. -/
theorem kernelMatrix_markerKernel {τ ν : Type*} (s : ℝ) (Z' : Matrix τ ι ℝ) (Z : Matrix ν ι ℝ) :
    kernelMatrix (markerKernel s) Z' Z = s • (Z' * Zᵀ) := by
  ext i j
  simp [kernelMatrix, markerKernel, Matrix.mul_apply, dotProduct]

omit [DecidableEq ι] in
/-- For `s ≥ 0` the marker kernel is a covariance kernel: its kernel matrix on any inputs is
positive semidefinite. -/
theorem kernelMatrix_markerKernel_posSemidef {ν : Type*} [Finite ν] {s : ℝ} (hs : 0 ≤ s)
    (Z : Matrix ν ι ℝ) : (kernelMatrix (markerKernel s) Z Z).PosSemidef := by
  rw [kernelMatrix_markerKernel]
  have h1 : (Z * Zᵀ).PosSemidef := by
    have := posSemidef_self_mul_conjTranspose Z
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  exact h1.smul hs

omit [DecidableEq ι] in
/-- **GP posterior mean = GBLUP**: for the marker kernel with variance `s > 0` and noise variance
`σ² > 0`, the predictive-mean matrix `K(Z', Z) (K(Z, Z) + σ² I)⁻¹` of Gaussian-process
regression is `Z' Zᵀ (ZZᵀ + (σ²/s) I)⁻¹`. -/
theorem gpMean_markerKernel {τ : Type*} {s σ2 : ℝ} (hs : 0 < s) (hσ : 0 < σ2)
    (Z' : Matrix τ ι ℝ) (Z : Matrix (Fin m) ι ℝ) :
    kernelMatrix (markerKernel s) Z' Z *
        (kernelMatrix (markerKernel s) Z Z + σ2 • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ =
      Z' * Zᵀ * (Z * Zᵀ + (σ2 / s) • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ := by
  have hB : IsUnit (Z * Zᵀ + (σ2 / s) • (1 : Matrix (Fin m) (Fin m) ℝ)).det :=
    (posDef_mul_transpose_add Z (div_pos hσ hs)).det_pos.ne'.isUnit
  have hK : kernelMatrix (markerKernel s) Z Z + σ2 • (1 : Matrix (Fin m) (Fin m) ℝ) =
      s • (Z * Zᵀ + (σ2 / s) • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    rw [kernelMatrix_markerKernel, smul_add, smul_smul, mul_div_cancel₀ _ hs.ne']
  have hinv : (s • (Z * Zᵀ + (σ2 / s) • (1 : Matrix (Fin m) (Fin m) ℝ)))⁻¹ =
      s⁻¹ • (Z * Zᵀ + (σ2 / s) • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs.ne', one_smul,
      nonsing_inv_mul _ hB]
  rw [hK, kernelMatrix_markerKernel, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ hs.ne', one_smul]

/-- **GP posterior mean = RR-BLUP**: with the marker kernel, the GP predictive mean at genotypes
`Z'` is `Z' β̂` for the ridge marker effects `β̂` with `λ = σ²/s`. -/
theorem gpMean_markerKernel_mulVec {τ : Type*} {s σ2 : ℝ} (hs : 0 < s)
    (hσ : 0 < σ2) (Z' : Matrix τ ι ℝ) (Z : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) :
    (kernelMatrix (markerKernel s) Z' Z *
        (kernelMatrix (markerKernel s) Z Z + σ2 • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹) *ᵥ y =
      Z' *ᵥ ridgeEstimate Z y (σ2 / s) := by
  rw [gpMean_markerKernel hs hσ, mulVec_ridgeEstimate Z' Z y (div_pos hσ hs)]

variable {τ : Type*} [Fintype τ] [DecidableEq τ]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [DecidableEq ι] in
/-- **The GBLUP posterior**: if the genetic values `Z' β` of individuals with genotypes `Z'` and
the phenotypes `y = Z β + ε` of the training individuals are jointly Gaussian with the covariance
of the marker kernel (marker-effect variance `s > 0`, residual variance `σ² > 0`), then given `y`
the genetic values are Gaussian with mean `Z' Zᵀ (ZZᵀ + (σ²/s) I)⁻¹ y`, which is the RR-BLUP
prediction `Z' β̂` (`gpMean_markerKernel_mulVec`), and covariance
`s (Z' Z'ᵀ - Z' Zᵀ (ZZᵀ + (σ²/s) I)⁻¹ Z Z'ᵀ)`. -/
theorem condDistrib_markerKernel {s σ2 : ℝ} (hs : 0 < s) (hσ : 0 < σ2) (Z' : Matrix τ ι ℝ)
    (Z : Matrix (Fin m) ι ℝ) {V : Ω → EuclideanSpace ℝ (τ ⊕ Fin m)} (hV : Measurable V)
    (hlaw : P.map V = multivariateGaussian 0 (jointCov (markerKernel s) σ2 Z' Z)) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin (targetPart (τ := τ)) (V ω)),
      condDistrib (fun ω => toEuclideanLin (testPart (ν := Fin m)) (V ω))
          (fun ω => toEuclideanLin (targetPart (τ := τ)) (V ω)) P y =
        multivariateGaussian
          (toEuclideanLin (Z' * Zᵀ * (Z * Zᵀ + (σ2 / s) • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹) y)
          (s • (Z' * Z'ᵀ - Z' * Zᵀ * (Z * Zᵀ + (σ2 / s) • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *
            (Z * Z'ᵀ))) := by
  have hk : (kernelMatrix (markerKernel s) (Sum.elim Z' Z) (Sum.elim Z' Z)).PosSemidef :=
    kernelMatrix_markerKernel_posSemidef hs.le (Sum.elim Z' Z : (τ ⊕ Fin m) → ι → ℝ)
  have h := condDistrib_test_given_targets (markerKernel s) hσ Z' Z hk hV hlaw
  rw [gpMean_markerKernel hs hσ, kernelMatrix_markerKernel, kernelMatrix_markerKernel] at h
  simpa only [smul_sub, Matrix.mul_smul] using h

/-! ### The RKHS view -/

open MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem in
/-- **Kernel ridge regression = GBLUP = RR-BLUP**: in a real RKHS whose kernel has Gram matrix
`ZZᵀ` at the training inputs, the kernel ridge fit (the minimizer of
`∑ᵢ (yᵢ - f xᵢ)² + λ ‖f‖²`, `kernelRidgeRisk_kernelRidgeFit_le`) has fitted values `Z β̂`. -/
theorem kernelRidgeFit_eq_mulVec_ridgeEstimate {X H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H X ℝ] (x : Fin m → X)
    (Z : Matrix (Fin m) ι ℝ) (hK : kernelGram H x = Z * Zᵀ) (y : Fin m → ℝ) {lam : ℝ}
    (hlam : 0 < lam) (j : Fin m) :
    kernelRidgeFit H x y lam (x j) = (Z *ᵥ ridgeEstimate Z y lam) j := by
  rw [kernelRidgeFit_apply, hK, mulVec_ridgeEstimate Z Z y hlam]

end Cslib.MachineLearning.GBLUP
