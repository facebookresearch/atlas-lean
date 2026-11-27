/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NagellLjunggrenFiveCube

open MetaMathlibExt

-- At the first permitted exponent, the quotient for base three is a square.
example (y : ℕ) (hy : 2 ≤ y) : (3 ^ 5 - 1) / (3 - 1) ≠ y ^ 3 :=
  nagell_ljunggren_cube_of_five_dvd 3 y 5 (hx := by decide) (hy := hy)
    (hn := by decide) (h5 := by decide)

-- The composite exponent tests the factor with reduced base 4 ^ 2 ≡ 1 modulo 5.
example (y : ℕ) (hy : 2 ≤ y) : (4 ^ 10 - 1) / (4 - 1) ≠ y ^ 3 :=
  nagell_ljunggren_cube_of_five_dvd 4 y 10 (hx := by decide) (hy := hy)
    (hn := by decide) (h5 := by decide)
