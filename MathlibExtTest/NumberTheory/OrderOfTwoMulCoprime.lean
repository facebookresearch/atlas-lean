/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OrderOfTwoMulCoprime

open MetaMathlibExt

-- The two orders share a factor, so their least common multiple is 4.
example : orderOf (2 : ZMod 15) = 4 := by
  have h₃ : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
  have h₅ : orderOf (2 : ZMod 5) = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
  rw [orderOf_two_mul_coprime (m₁ := 3) (m₂ := 5) (by decide) (by decide) (by decide), h₃, h₅]
  decide

-- The unique residue modulo one has order one.
example {m : ℕ} (hm : Odd m) : orderOf (2 : ZMod (1 * m)) = orderOf (2 : ZMod m) := by
  rw [orderOf_two_mul_coprime (by decide) hm (Nat.coprime_one_left m),
    Subsingleton.elim (2 : ZMod 1) 1, orderOf_one, Nat.lcm_one_left]
