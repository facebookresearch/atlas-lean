/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NagellLjunggrenCubeNoSolution

open MetaMathlibExt

-- The lower endpoint for the exponent and a base divisible by three.
example (y : ℤ) : 6 ^ 3 - 1 ≠ (6 - 1) * y ^ 3 :=
  nagell_ljunggren_cube_no_solution 3 (by decide) 6 y (by decide)

-- A negative base in the odd exponent case.
example (y : ℤ) : (-4) ^ 7 - 1 ≠ (-4 - 1) * y ^ 3 :=
  nagell_ljunggren_cube_no_solution 7 (by decide) (-4) y (by decide)

-- With a negative base and an even exponent, a putative cube root would be negative.
example (y : ℤ) : (-7) ^ 18 - 1 ≠ (-7 - 1) * y ^ 3 :=
  nagell_ljunggren_cube_no_solution 18 (by decide) (-7) y (by decide)
