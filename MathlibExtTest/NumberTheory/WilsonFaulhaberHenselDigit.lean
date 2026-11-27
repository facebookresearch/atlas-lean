/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.WilsonFaulhaberHenselDigit

open MathlibExt.NumberTheory.WilsonFaulhaberWanted

-- The least prime requires no oddness assumption: k = 1 and t = 1.
example : ((((2 : ℕ) : ℤ) * 1 : ℤ) : ZMod (2 ^ 2)) = 2 := by
  rw [hensel_digit_mul_prime_mod_sq 2 (by decide) 1 (by decide) 1 (by decide)]
  decide

-- A negative lift representative with a nonzero Fermat quotient.
example : ((((3 : ℕ) : ℤ) * (-2) : ℤ) : ZMod (3 ^ 2)) = 3 := by
  rw [hensel_digit_mul_prime_mod_sq 3 (by decide) 2 (by decide) (-2) (by decide)]
  decide

-- For p = 5 and k = 2 the root is represented by 7 modulo 25.
example : ((((5 : ℕ) : ℤ) * 1 : ℤ) : ZMod (5 ^ 2)) = 5 := by
  rw [hensel_digit_mul_prime_mod_sq 5 (by decide) 2 (by decide) 1 (by decide)]
  decide
