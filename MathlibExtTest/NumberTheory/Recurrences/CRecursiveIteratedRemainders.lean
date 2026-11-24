/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CRecursiveIteratedRemainders

/-! # Tests for iterated remainders in the positive residue case -/

open MetaMathlibExt

-- The quotient 6 reduces to 1, and the inner remainder 9 reduces to 4, one below the modulus.
example : ((-75 : ℤ) % 12) % 5 = 4 :=
  neg_emod_emod_eq_mul_one_add_ediv_emod_of_pos 2 75 12 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- At equality in the strict bound the product is 6, so the outer remainder wraps to zero.
example : ((-18 : ℤ) % 8) % 6 = 0 ∧ 2 * (1 + ((18 : ℤ) / 8) % 6) = 6 := by decide
