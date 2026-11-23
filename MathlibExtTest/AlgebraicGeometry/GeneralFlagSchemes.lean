/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.GeneralFlagSchemes

/-!
# Tests for partial-flag shapes and dimensions

`flagDimension` counts the pairs of distinct blocks of a partial flag, with the
endpoints `0` and `n` implicit.
-/

open MathlibExt.AlgebraicGeometry.GeneralFlagSchemes

/-- The complete flag variety of `ℂ³` has dimension `3`. -/
example : flagDimension (fullShape 3) = 3 := by decide

/-- The complete flag variety of `ℂ⁴` has dimension `6`. -/
example : flagDimension (fullShape 4) = 6 := by decide

/-- The Grassmannian of planes in `ℂ⁴` has dimension `4`; the final block
`4 - 2` counts although `4` is not a selected rank. -/
example : flagDimension ({2} : Shape 4) = 4 := by decide

/-- Projective space of lines in `ℂ³`. -/
example : flagDimension ({1} : Shape 3) = 2 := by decide

/-- Omitting the line from a complete flag of `ℂ³` leaves `Gr(2, 3)`. -/
example : flagDimension (omittedShape 3 1) = 2 := by decide

/-- Selecting only the endpoints gives a point. -/
example : flagDimension ({0, Fin.last 3} : Shape 3) = 0 := by decide

/-- Blocks of the shape `{1, 3}` in `ℂ⁴`: sizes `1`, `2` and the implicit last `1`. -/
example : blockSize ({1, 3} : Shape 4) 1 = 1 ∧ blockSize ({1, 3} : Shape 4) 3 = 2 ∧
    blockSize ({1, 3} : Shape 4) (Fin.last 4) = 1 := by decide
