/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimePowAddOneEqSq

open MetaMathlibExt

example : 2 ^ 3 + 1 = (3 : ℕ) ^ 2 :=
  (prime_pow_add_one_eq_sq_iff Nat.prime_two 3 3).2 (Or.inl rfl)

example : 3 ^ 1 + 1 = (2 : ℕ) ^ 2 :=
  (prime_pow_add_one_eq_sq_iff Nat.prime_three 1 2).2 (Or.inr rfl)

example {p : ℕ} (hp : p.Prime) (y : ℕ) : p ^ 0 + 1 ≠ y ^ 2 := by
  rw [ne_eq, prime_pow_add_one_eq_sq_iff hp]
  simp
