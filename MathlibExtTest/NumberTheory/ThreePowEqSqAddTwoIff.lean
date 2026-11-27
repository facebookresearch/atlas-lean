/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreePowEqSqAddTwoIff

open MetaMathlibExt

example : 3 ^ 1 = (1 : Nat) ^ 2 + 2 :=
  (three_pow_eq_sq_add_two_iff 1 1).2 (Or.inl rfl)

example : 3 ^ 3 = (5 : Nat) ^ 2 + 2 :=
  (three_pow_eq_sq_add_two_iff 3 5).2 (Or.inr rfl)

example (x y : Nat) (h : 3 ^ x = y ^ 2 + 2) : x = 1 ∨ x = 3 := by
  have sol := (three_pow_eq_sq_add_two_iff x y).1 h
  rcases sol with h' | h' <;> simp only [Prod.mk.injEq] at h' <;> omega

example (y : Nat) : 3 ^ 2 ≠ y ^ 2 + 2 := by
  intro h
  have sol := (three_pow_eq_sq_add_two_iff 2 y).1 h
  simp only [Prod.mk.injEq] at sol
  omega

example (y : Nat) : 3 ^ 5 ≠ y ^ 2 + 2 := by
  intro h
  have sol := (three_pow_eq_sq_add_two_iff 5 y).1 h
  simp only [Prod.mk.injEq] at sol
  omega
