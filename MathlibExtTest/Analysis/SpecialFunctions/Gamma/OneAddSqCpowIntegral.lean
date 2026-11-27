/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.OneAddSqCpowIntegral

@[expose] public section

/-- `exactSource` consumer with the original binders. -/
example (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = Complex.Gammaℝ (2 * s) / Complex.Gammaℝ (2 * s + 1) :=
  AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div s hs

/-- Boundary example at `s = 1`: both sides are concrete, and the formula
specialises to `Gammaℝ 2 / Gammaℝ 3`. -/
example :
    ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-((1 : ℂ) + 1 / 2))
      = Complex.Gammaℝ (2 * 1) / Complex.Gammaℝ (2 * 1 + 1) :=
  AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div 1 (by norm_num)
