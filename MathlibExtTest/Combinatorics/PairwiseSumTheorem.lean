/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Log
import MathlibExt.Combinatorics.PairwiseSumTheorem

/-! # Test for the pairwise sum theorem -/

namespace MetaMathlibExt.exists_infinite_pairwiseSums_monochromatic

-- Alternating the colors of successive dyadic intervals shows why the summands must be distinct.
example : ∃ (c : ℕ → Fin 2) (A : Set ℕ) (k : Fin 2), A.Infinite ∧
    (∀ a ∈ A, c a = k) ∧ (∀ a ∈ A, ∀ b ∈ A, a ≠ b → c (a + b) = k) ∧
    (∀ a ∈ A, 0 < a → c (a + a) ≠ k) := by
  let c (n : ℕ) : Fin 2 := ⟨Nat.log 2 n % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨A, hA, k, hmem, hpair⟩ := exists_infinite_pairwiseSums_monochromatic c
  refine ⟨c, A, k, hA, hmem, hpair, ?_⟩
  intro a ha hpos
  rw [← hmem a ha]
  intro h
  have heq := congrArg Fin.val h
  change Nat.log 2 (a + a) % 2 = Nat.log 2 a % 2 at heq
  rw [← Nat.mul_two, Nat.log_mul_base Nat.one_lt_two hpos.ne'] at heq
  omega

end MetaMathlibExt.exists_infinite_pairwiseSums_monochromatic
