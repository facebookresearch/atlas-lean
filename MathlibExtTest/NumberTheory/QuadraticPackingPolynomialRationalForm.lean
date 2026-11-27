/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticPackingPolynomialRationalForm
import all MathlibExtTest.NumberTheory.QuadraticPackingPolynomialsStaircaseCongruence
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

open quadraticPackingPolynomial_staircase_congruence.Test

-- The slope-12/7 example has shear coefficient 1/2 and y² coefficient 3/2.
example : ∃ D E F : ℤ, ∀ x y, examplePolynomial x y =
    6 * (x - y / 2) ^ 2 + (D - 6) * x + (E - 3 / 2) * y + F := by
  obtain ⟨_, D, E, F, h⟩ := quadraticPackingPolynomial_rational_sector_form
    (by decide) (by decide) (by decide) packing_example
  refine ⟨D, E, F, fun x y => ?_⟩
  rw [h]
  norm_num
  ring

-- For slope 3/2 the required divisibility fails.
example : ¬ ∃ P : ℝ → ℝ → ℝ,
    IsQuadraticPackingPolynomial (sectorLatticePoints (3 / 2)) P := by
  rintro ⟨P, hP⟩
  have h := (quadraticPackingPolynomial_rational_sector_form (m := 2) (n := 3)
    (by decide) (by decide) (by decide) hP).1
  norm_num at h

end MetaMathlibExt
