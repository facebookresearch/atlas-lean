/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.VectorGaussianKernelKL

@[expose] public section

open MathlibExt.InformationTheory.VectorGaussianKernelKL MeasureTheory ProbabilityTheory
  InformationTheory Matrix

namespace MathlibExtTest.InformationTheory.VectorGaussianKernelKL

/-- A point input whose channel mean equals the comparison mean, with equal noise and comparison
covariances, gives divergence zero. -/
example :
    klDiv ((Measure.dirac (WithLp.toLp 2 ![1, 2])) ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (MetaMathlibExt.continuous_toEuclideanLin _).measurable (multivariateGaussian 0 1))
      ((Measure.dirac (WithLp.toLp 2 ![1, 2])).prod
        (multivariateGaussian (WithLp.toLp 2 ![1, 2]) 1)) = 0 := by
  rw [klDiv_compProd_noiseKernel_dirac _ _ _ _ PosDef.one PosDef.one, gaussianKernelKLReal_dirac,
    MetaMathlibExt.toEuclideanLin_one_apply]
  simp

/-- A large input mean contributes through the quadratic term: with identity channel and
covariances, the point input `(10, 0)` against `N(0, 1)` has divergence `10² / 2 = 50`. -/
example :
    klDiv ((Measure.dirac (WithLp.toLp 2 ![10, 0])) ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (MetaMathlibExt.continuous_toEuclideanLin _).measurable (multivariateGaussian 0 1))
      ((Measure.dirac (WithLp.toLp 2 ![10, 0])).prod (multivariateGaussian 0 1)) =
      ENNReal.ofReal 50 := by
  rw [klDiv_compProd_noiseKernel_dirac _ _ _ _ PosDef.one PosDef.one, gaussianKernelKLReal_dirac,
    MetaMathlibExt.toEuclideanLin_one_apply]
  congr 1
  simp [dotProduct, Fin.sum_univ_two]
  norm_num

/-- Different noise and comparison covariances on a point input at the comparison mean, in
dimension `1`: `R = 1` and `T = 2` give `(log 2 - 1 + 1 / 2) / 2`. -/
example :
    gaussianKernelKLReal (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 1 ((2 : ℝ) • 1) (Measure.dirac 0) =
      (Real.log 2 - 1 + 1 / 2) / 2 := by
  have hinv : ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = (2⁻¹ : ℝ) • 1 :=
    inv_eq_left_inv (by
      rw [smul_mul_smul_comm, inv_mul_cancel₀ two_ne_zero, Matrix.one_mul, one_smul])
  rw [gaussianKernelKLReal_dirac, hinv]
  simp

/-- A Gaussian input with singular covariance `diag(1, 0)` through the channel `H = [1 1]`:
the input contributes `trace (T⁻¹ H S Hᵀ) = 1`, so with `R = T = 1` and centered means the
divergence is `1 / 2`. -/
example :
    klDiv ((multivariateGaussian 0 (diagonal ![1, 0])) ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin !![(1 : ℝ), 1])
          (MetaMathlibExt.continuous_toEuclideanLin _).measurable
          (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)))
      ((multivariateGaussian 0 (diagonal ![1, 0])).prod (multivariateGaussian 0 1)) =
      ENNReal.ofReal (1 / 2) := by
  have hS : (diagonal ![(1 : ℝ), 0]).PosSemidef :=
    posSemidef_diagonal_iff.2 fun i => by fin_cases i <;> simp
  rw [klDiv_compProd_noiseKernel _ _ _ _ PosDef.one PosDef.one _ IsGaussian.memLp_two_id,
    gaussianKernelKLReal_gaussianInput _ _ _ _ _ _ hS]
  congr 1
  simp [vecMul, dotProduct, mul_apply, Fin.sum_univ_two, trace_fin_one]

end MathlibExtTest.InformationTheory.VectorGaussianKernelKL
