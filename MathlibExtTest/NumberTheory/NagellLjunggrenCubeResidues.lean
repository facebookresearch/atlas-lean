/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NagellLjunggrenCubeResidues

open MetaMathlibExt

-- The smallest admissible exponent, with a base divisible by three.
example (y : ℤ) : 3 ^ 5 - 1 ≠ (3 - 1) * y ^ 3 :=
  nagell_ljunggren_cube_no_solution_of_mod_six_eq_five 5 (by decide) 3 y (by decide)

-- A negative base in the unit class five and an exponent in the next period.
example (y : ℤ) : (-4) ^ 11 - 1 ≠ (-4 - 1) * y ^ 3 :=
  nagell_ljunggren_cube_no_solution_of_mod_six_eq_five 11 (by decide) (-4) y (by decide)
