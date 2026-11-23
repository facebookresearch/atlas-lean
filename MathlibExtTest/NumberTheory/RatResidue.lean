/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RatResidue
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- The residue of `1/2` modulo `5` is the inverse `3` of `2`, since `2 * 3 = 6 ≡ 1 (mod 5)`.
example : ratResidue 5 (1 / 2) = 3 := by
  rw [ratResidue, show (1 / 2 : ℚ).num = 1 by simp, show (1 / 2 : ℚ).den = 2 by simp,
    ZMod.inv_eq_of_mul_eq_one 5 _ 3 (by decide)]
  decide

-- The residue reads the reduced fraction: `2/4 = 1/2` has the same residue modulo `5`.
example : ratResidue 5 (2 / 4) = ratResidue 5 (1 / 2) := by
  norm_num

-- On integers the residue is the usual cast: `-1 ≡ 6 (mod 7)`.
example : ratResidue 7 (-1) = 6 := by
  rw [show (-1 : ℚ) = ((-1 : ℤ) : ℚ) by norm_num, ratResidue_intCast]
  decide

-- An integer multiple of the modulus has residue `0`.
example (z : ℤ) : ratResidue 3 (3 * z) = 0 := by
  rw [show (3 * z : ℚ) = ((3 * z : ℤ) : ℚ) by norm_num, ratResidue_intCast]
  push_cast
  rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]

end MetaMathlibExt
