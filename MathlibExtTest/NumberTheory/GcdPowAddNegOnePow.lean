/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GcdPowAddNegOnePow

/-!
# Boundary cases for the two gcd identities
-/

namespace MetaMathlibExt

-- At the smallest exponent the signed sum is just the ordinary sum.
example {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (huv : u.Coprime v) :
    Int.gcd ((u : ℤ) + v) u = 1 ∧ Int.gcd ((u : ℤ) + v) v = 1 := by
  simpa using gcd_pow_add_neg_one_pow_mul_eq_one (N := 1) le_rfl hu hv huv

-- With an even exponent, the first gcd argument can be negative or zero.
example : Int.gcd (-5) 2 = 1 ∧ Int.gcd (-5) 9 = 1 :=
  gcd_pow_add_neg_one_pow_mul_eq_one (N := 2) (u := 2) (v := 9)
    (by decide) (by decide) (by decide) (by decide)

example : Int.gcd 0 1 = 1 ∧ Int.gcd 0 1 = 1 :=
  gcd_pow_add_neg_one_pow_mul_eq_one (N := 2) (u := 1) (v := 1)
    (by decide) (by decide) (by decide) (by decide)

end MetaMathlibExt
