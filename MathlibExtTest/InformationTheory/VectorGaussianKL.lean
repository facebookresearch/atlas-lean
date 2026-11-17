/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.VectorGaussianKL

@[expose] public section

open MathlibExt.InformationTheory.VectorGaussianKL MeasureTheory ProbabilityTheory InformationTheory

namespace MathlibExtTest.InformationTheory.VectorGaussianKL

/-- The headline formula for a Gaussian against itself gives KL divergence zero. -/
example (m : EuclideanSpace ℝ (Fin 2)) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.PosDef) :
    klDiv (multivariateGaussian m S) (multivariateGaussian m S) = 0 := by
  rw [klDiv_multivariateGaussian m m S S hS hS, multivariateGaussianKLReal_self m S hS,
    ENNReal.ofReal_zero]

/-- The headline formula on a concrete nondiagonal covariance:
`KL(N((1,0), 1) ‖ N(0, [[2,1],[1,2]])) = ofReal (log 3 / 2)`. -/
example :
    klDiv (multivariateGaussian (WithLp.toLp 2 ![1, 0]) (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (multivariateGaussian 0 !![2, 1; 1, 2]) =
      ENNReal.ofReal (Real.log 3 / 2) :=
  klDiv_multivariateGaussian_nondiagonal

/-- Equal covariances with a nonzero mean difference: `KL(N((1,0), 1) ‖ N(0, 1))` is half the
squared mean distance, `1 / 2`. -/
example :
    klDiv (multivariateGaussian (WithLp.toLp 2 ![1, 0]) (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (multivariateGaussian 0 1) =
      ENNReal.ofReal (1 / 2) := by
  rw [klDiv_multivariateGaussian_same_covariance _ _ _ Matrix.PosDef.one]
  simp [dotProduct, Fin.sum_univ_two]

/-- A zero covariance gives a point mass, singular to a nondegenerate Gaussian: divergence `⊤`. -/
example (m q : EuclideanSpace ℝ (Fin 2)) :
    klDiv (multivariateGaussian m 0) (multivariateGaussian q (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      ⊤ :=
  klDiv_multivariateGaussian_zero_covariance m q 1 Matrix.PosDef.one

end MathlibExtTest.InformationTheory.VectorGaussianKL
