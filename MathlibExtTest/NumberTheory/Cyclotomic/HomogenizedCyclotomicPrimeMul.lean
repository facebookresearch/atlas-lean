/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomicPrimeMul

/-! # Tests for homogenized cyclotomic values at prime multiples -/

open MetaMathlibExt

-- At index four the second argument can vanish.
example (a : ℤ) : homogenizedCyclotomic 4 a 0 = a ^ 2 := by
  simpa [homogenizedCyclotomic_two] using
    (homogenizedCyclotomic_prime_mul Nat.prime_two (by decide : 0 < 2) a 0).1 (by decide)

-- The product identity allows negative arguments.
example : homogenizedCyclotomic 6 (-5) 2 * homogenizedCyclotomic 2 (-5) 2 = -117 := by
  rw [(homogenizedCyclotomic_prime_mul Nat.prime_three (by decide : 0 < 2) (-5) 2).2
    (by decide), homogenizedCyclotomic_two]
  norm_num

-- With opposite arguments the factor of index two in the product vanishes.
example (a : ℤ) : homogenizedCyclotomic 6 a (-a) * homogenizedCyclotomic 2 a (-a) = 0 := by
  rw [(homogenizedCyclotomic_prime_mul Nat.prime_three (by decide : 0 < 2) a (-a)).2
    (by decide), homogenizedCyclotomic_two]
  ring
