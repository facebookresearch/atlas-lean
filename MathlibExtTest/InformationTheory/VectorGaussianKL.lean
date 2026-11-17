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

/-- A Gaussian against itself has KL divergence zero. -/
example (m : EuclideanSpace ℝ (Fin 2)) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.PosDef) :
    klDiv (multivariateGaussian m S) (multivariateGaussian m S) = 0 := by
  rw [klDiv_multivariateGaussian_self m S hS, multivariateGaussianKLReal_self m S hS,
    ENNReal.ofReal_zero]

end MathlibExtTest.InformationTheory.VectorGaussianKL
