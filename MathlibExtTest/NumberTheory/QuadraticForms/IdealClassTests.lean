/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.IdealClass

/-!
# Binary quadratic form ideal-class regression checks

Concrete positive forms test the field degree, quadratic-form evaluation, and nonzero ideal.
-/

open BinaryQuadraticForm

example : Module.finrank ℚ (imaginaryQuadraticField 3) = 2 :=
  imaginaryQuadraticField_finrank 3 (by decide)

example : Module.finrank ℚ (imaginaryQuadraticField 4) = 2 :=
  imaginaryQuadraticField_finrank 4 (by decide)

example : ofCoefficients (1, 1, 1) (-2, 3) = 7 := by
  rw [ofCoefficients_apply]
  norm_num

example : (ofCoefficients (1, 1, 1)).PosDef :=
  ofCoefficients_posDef 3 (by decide) (1, 1, 1) (by decide) (by norm_num [discrim])

example : (ofCoefficients (1, 0, 1)).PosDef :=
  ofCoefficients_posDef 4 (by decide) (1, 0, 1) (by decide) (by norm_num [discrim])

example : formIdeal 3 (1, 1, 1) ≠ 0 :=
  formIdeal_ne_zero 3 (1, 1, 1) (by decide)
