/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.CommonCovarianceLikelihood
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Probability.Distributions.CommonCovarianceLikelihood
open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Distributions.CommonCovarianceLikelihood

/-- Equal means give log-likelihood ratio `0` at a concrete point. -/
example : commonCovarianceLogLR (0 : EuclideanSpace ℝ (Fin 2)) 0 1 0 = 0 :=
  commonCovarianceLogLR_self 0 1 0

/-- Equal means give Radon--Nikodym derivative `1` for the
identity covariance, with the canonical density discharged. -/
example : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 1).rnDeriv
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 1)
    =ᵐ[volume] fun _ => 1 :=
  rnDeriv_multivariateGaussian_self_eq_one 0 1 Matrix.PosDef.one

/-- Absolute continuity between the two unit Gaussians with
different means, density discharged. -/
example : multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 1
    ≪ multivariateGaussian (EuclideanSpace.single 0 1) 1 :=
  multivariateGaussian_absolutelyContinuous_common_covariance 0
    (EuclideanSpace.single 0 1) 1 Matrix.PosDef.one

end MathlibExtTest.Probability.Distributions.CommonCovarianceLikelihood
