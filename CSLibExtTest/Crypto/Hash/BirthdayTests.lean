/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Hash.Birthday
public import Mathlib.Tactic.NormNum

/-!
# Tests for the birthday bound

* Two fair coin flips (`α = Bool`, `q = 2`) collide with probability exactly `1/2`.
* One sample never collides; `N + 1` samples always collide (pigeonhole).
* Birthdays (`N = 365`): 10 people collide with probability between `90 / 1460` and `90 / 730`,
  and 28 people collide with probability at least `1/2` (the true threshold is 23; the bound
  `x / (1 + x)` is not tight).
-/

@[expose] public section

namespace Cslib.Crypto.BirthdayTests

open Cslib.Crypto.Birthday

example : collisionProb Bool 2 = 1 / 2 := by
  rw [collisionProb_eq]
  norm_num [Nat.descFactorial]

example (α : Type*) [Fintype α] [Nonempty α] : collisionProb α 1 = 0 := by
  have : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [collisionProb_eq, Nat.descFactorial_one, pow_one, div_self this.ne', sub_self]

example (α : Type*) [Fintype α] [Nonempty α] : collisionProb α (Fintype.card α + 1) = 1 := by
  rw [collisionProb_eq, Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_succ_self _)]
  simp

example : collisionProb (Fin 365) 10 ≤ 90 / 730 := by
  have := collisionProb_le (Fin 365) 10
  norm_num at this ⊢
  linarith

example : 90 / 1460 ≤ collisionProb (Fin 365) 10 := by
  have := collisionProb_ge (Fin 365) 10 (by norm_num)
  norm_num at this ⊢
  linarith

example : 90 / 1460 ≤ collisionProb (Fin 365) 10 := by
  have := collisionProb_ge_of_le_sqrt (Fin 365) 10 (by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num)
  norm_num at this ⊢
  linarith

example : 90 / 1460 ≤ collisionProb (Fin 365) 10 := by
  have := collisionProb_ge_of_le_sqrt_card (Fin 365) 10 (by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num)
  norm_num at this ⊢
  linarith

example : 1 / 2 ≤ collisionProb (Fin 365) 28 :=
  half_le_collisionProb (Fin 365) 28 (by norm_num)

end Cslib.Crypto.BirthdayTests
