/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.GaussianDensity

open MetaMathlibExt MeasureTheory ProbabilityTheory Matrix WithLp

-- The density of a positive definite multivariate Gaussian in three dimensions.
example (μ : EuclideanSpace ℝ (Fin 3)) (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosDef) :
    multivariateGaussian μ S =
      volume.withDensity fun x => ENNReal.ofReal (multivariateGaussianPDFReal μ S x) :=
  multivariateGaussian_eq_withDensity μ hS

-- With `μ = 0` and `S = 1` the formula is the standard Gaussian density.
example (x : EuclideanSpace ℝ (Fin 3)) :
    multivariateGaussianPDFReal 0 (1 : Matrix (Fin 3) (Fin 3) ℝ) x = stdGaussianPDFReal x := by
  rw [multivariateGaussianPDFReal, stdGaussianPDFReal, sub_zero, inv_one, one_mulVec, det_one,
    Real.sqrt_one, inv_one, mul_one, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

-- The standard Gaussian density.
example : stdGaussian (EuclideanSpace ℝ (Fin 2)) =
    volume.withDensity fun v => ENNReal.ofReal (stdGaussianPDFReal v) :=
  stdGaussian_eq_withDensity

#print axioms multivariateGaussian_eq_withDensity
