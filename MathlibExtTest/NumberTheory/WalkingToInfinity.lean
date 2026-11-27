/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.NumberTheory.WalkingToInfinity

open MetaMathlibExt

-- The smallest admissible pair gives 4 - 1 = 3.
example : ¬ ∃ m : ℕ, 3 = 2 ^ m :=
  two_pow_sub_succ_ne_two_pow 0 2 (by decide)

-- For p + 1 = 5 the ceiling logarithm rounds up, and k = 5 gives 32 - 5 = 27.
example : ¬ ∃ m : ℕ, 27 = 2 ^ m :=
  two_pow_sub_succ_ne_two_pow 4 5 (by decide)

-- One exponent below the bound, subtracting a power of two can give it back.
example (r : ℕ) : 2 ^ (r + 1) - 2 ^ r = 2 ^ r := by
  rw [Nat.pow_succ]
  omega

-- Starting at 3 permits two successive leading-zero blocks: 3 → 13 → 53.
example : ∃ p : Fin 3 → ℕ, (∀ i, (p i).Prime) ∧
    ∀ i : Fin 2, p i.succ = 2 ^ 2 * p i.castSucc + 1 :=
  ⟨![3, 13, 53], by decide, by decide⟩

-- Any infinite continuation by the permitted blocks has a nonprime term.
example (p : ℕ → ℕ)
    (hs : ∀ i, ∃ n k : ℕ, 1 ≤ n ∧ n ≤ 2 ∧ k < 2 ^ n ∧ p (i + 1) = 2 ^ n * p i + k) :
    ∃ i, ¬ (p i).Prime := by
  by_contra! hp
  exact not_exists_binary_prime_walk_appending_at_most_two_digits ⟨p, hp, hs⟩
