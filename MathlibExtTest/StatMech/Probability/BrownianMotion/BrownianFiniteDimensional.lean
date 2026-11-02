/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianFiniteDimensional
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianFiniteDimensional`

* `brownianCovariance` at concrete times: `c(1, 2) = 1`, `c(-1, 1) = 0`, `c(-2, -3) = 2`, and the
  bridge `brownianCovariance_of_nonneg` to `min s t`.
* The finite-dimensional law at `I = {0, 1}`: a probability measure; the increment from `0` to `1`
  is `N(0, 1)`; the projective family property.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianFiniteDimensional

example : brownianCovariance 1 2 = 1 := by rw [brownianCovariance_eq]; norm_num

example : brownianCovariance (-1) 1 = 0 := by rw [brownianCovariance_eq]; norm_num

example : brownianCovariance (-2) (-3) = 2 := by rw [brownianCovariance_eq]; norm_num

example : brownianCovariance 3 5 = min 3 5 := brownianCovariance_of_nonneg (by norm_num) (by norm_num)

example : IsProbabilityMeasure (brownianFiniteDimensionalLaw {0, 1}) := inferInstance

/-- The times `0` and `1` as elements of `{0, 1}`. -/
def t0 : ({0, 1} : Finset ℝ) := ⟨0, by simp⟩
/-- The time `1` as an element of `{0, 1}`. -/
def t1 : ({0, 1} : Finset ℝ) := ⟨1, by simp⟩

example : MeasurePreserving (fun x : EuclideanSpace ℝ ({0, 1} : Finset ℝ) => x t1 - x t0)
    (brownianFiniteDimensionalLaw {0, 1}) (gaussianReal 0 1) := by
  simpa [t0, t1] using brownianFiniteDimensionalLaw_measurePreserving_increment {0, 1} t0 t1

example : @IsProjectiveMeasureFamily ℝ (fun _ => ℝ) (fun _ => inferInstance)
    brownianFiniteDimensionalPiLaw := brownianFiniteDimensionalPiLaw_isProjective

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianFiniteDimensional
