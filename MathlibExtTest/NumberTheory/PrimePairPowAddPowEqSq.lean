/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimePairPowAddPowEqSq

open MetaMathlibExt

example : 3 ^ 1 + 5 ^ 0 = (2 : ℕ) ^ 2 :=
  (prime_pair_pow_add_pow_eq_sq_iff (p := 3) (by decide) (by decide) (by decide) 1 0 2).2 rfl

example (x y z : ℕ) (hy : 0 < y) : 3 ^ x + 5 ^ y ≠ z ^ 2 := by
  intro h
  have sol := (prime_pair_pow_add_pow_eq_sq_iff (p := 3)
    (by decide) (by decide) (by decide) x y z).1 h
  simp only [Prod.mk.injEq] at sol
  omega

example (x y z : ℕ) : 7 ^ x + 13 ^ y ≠ z ^ 2 := by
  intro h
  have sol := (prime_pair_pow_add_pow_eq_sq_iff (p := 7)
    (by decide) (by decide) (by decide) x y z).1 h
  exact (by decide : (7 : ℕ) ≠ 3) (Prod.mk.inj sol).1
