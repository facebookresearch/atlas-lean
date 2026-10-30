/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianProductProcess
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianProductProcess`

* The coordinate process under `brownianProductLaw`: `B_1 ~ N(0, 1)`, `B_0 = 0` a.s., the increment
  from `-1` to `2` is `N(0, 3)`, increments over `[0, 1]` and `[1, 2]` are independent, it is a
  Gaussian process and a Kolmogorov process.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianProductProcess

example : HasLaw (brownianCoordinateProcess 1) (gaussianReal 0 1) brownianProductLaw := by
  simpa using brownianCoordinateProcess_eval_law 1

example : ∀ᵐ ω ∂brownianProductLaw, brownianCoordinateProcess 0 ω = 0 :=
  brownianCoordinateProcess_start

example : HasLaw (fun ω => brownianCoordinateProcess 2 ω - brownianCoordinateProcess (-1) ω)
    (gaussianReal 0 3) brownianProductLaw := by
  have h := brownianCoordinateProcess_increment_law (-1) 2
  norm_num at h
  exact h

example : IndepFun (fun ω => brownianCoordinateProcess 1 ω - brownianCoordinateProcess 0 ω)
    (fun ω => brownianCoordinateProcess 2 ω - brownianCoordinateProcess 1 ω) brownianProductLaw :=
  brownianCoordinateProcess_indep_increments 0 1 1 2 (by norm_num) le_rfl (by norm_num)

example : IsGaussianProcess brownianCoordinateProcess brownianProductLaw :=
  brownianCoordinateProcess_isGaussianProcess

example : IsKolmogorovProcess brownianCoordinateProcess brownianProductLaw 4 2 3 :=
  brownianCoordinateProcess_isKolmogorovProcess

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianProductProcess
