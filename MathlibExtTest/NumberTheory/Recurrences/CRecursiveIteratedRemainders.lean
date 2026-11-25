/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CRecursiveIteratedRemainders

/-! # Tests for iterated remainders -/

open MetaMathlibExt

-- The bounded product is 4, one below the outer modulus.
example : ((20 : ℤ) % 8) % 5 = 4 := by
  have ha : (-2 : ℤ) < 0 := by decide
  calc
    _ = |(-2 : ℤ)| * ((20 / 8) % 5) :=
      emod_emod_eq_abs_mul_ediv_emod_of_neg (-2) 20 8 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) ha (by rw [abs_of_neg ha]; decide)
    _ = 4 := by rw [abs_of_neg ha]; decide

-- The quotient 5 reduces to 0, so the bound holds even though |a| = 7 exceeds 5.
example : ((45 : ℤ) % 8) % 5 = 0 := by
  have ha : (-7 : ℤ) < 0 := by decide
  calc
    _ = |(-7 : ℤ)| * ((45 / 8) % 5) :=
      emod_emod_eq_abs_mul_ediv_emod_of_neg (-7) 45 8 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) ha (by rw [abs_of_neg ha]; decide)
    _ = 0 := by rw [abs_of_neg ha]; decide

-- The quotient 3 reduces to 1 at the smallest allowed modulus.
example : ((10 : ℤ) % 3) % 2 = 1 := by
  have ha : (-1 : ℤ) < 0 := by decide
  calc
    _ = |(-1 : ℤ)| * ((10 / 3) % 2) :=
      emod_emod_eq_abs_mul_ediv_emod_of_neg (-1) 10 3 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) ha (by rw [abs_of_neg ha]; decide)
    _ = 1 := by rw [abs_of_neg ha]; decide

-- The quotient 6 reduces to 1, and the inner remainder 9 reduces to 4, one below the modulus.
example : ((-75 : ℤ) % 12) % 5 = 4 :=
  neg_emod_emod_eq_mul_one_add_ediv_emod_of_pos 2 75 12 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- At equality in the strict bound the product is 6, so the outer remainder wraps to zero.
example : ((-18 : ℤ) % 8) % 6 = 0 ∧ 2 * (1 + ((18 : ℤ) / 8) % 6) = 6 := by decide
