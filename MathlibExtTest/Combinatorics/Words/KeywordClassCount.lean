/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Fib.Basic
import MathlibExt.Combinatorics.Words.KeywordClassCount

namespace MetaMathlibExt.card_quot_keywordEquiv_eq_sum_mStepFibonacci

-- Every two-bit keyword gives n + 1 classes, including at the minimum word length.
example (a : Fin 2 → Bool) (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Quot (KeywordEquiv (n := n) a)) = n + 1 := by
  simpa using card_quot_keywordEquiv_eq_sum_mStepFibonacci 1 n le_rfl hn (fun _ => 1) rfl
    (fun k hk hk' => by omega) (fun k _ => by simp) a

private theorem threeBitCount (a : Fin 3 → Bool) (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Quot (KeywordEquiv (n := n) a)) = ∑ j ∈ Finset.range (n + 1), Nat.fib (j + 1) := by
  apply card_quot_keywordEquiv_eq_sum_mStepFibonacci 2 n (by decide) hn _ rfl
  · intro k hk hk'
    obtain rfl : k = 1 := by omega
    rfl
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [Finset.sum_Icc_succ_top (by decide), Finset.Icc_self, Finset.sum_singleton,
      show j + 2 - 1 + 1 = j + 2 by omega, show j + 2 - (1 + 1) + 1 = j + 1 by omega,
      Nat.fib_add_two, add_comm]

-- The keyword is too long to apply, fits exactly once, or fits in two overlapping windows.
example (a : Fin 3 → Bool) : Nat.card (Quot (KeywordEquiv (n := 2) a)) = 4 := by
  rw [threeBitCount a 2 (by decide)]
  decide

example (a : Fin 3 → Bool) : Nat.card (Quot (KeywordEquiv (n := 3) a)) = 7 := by
  rw [threeBitCount a 3 (by decide)]
  decide

example (a : Fin 3 → Bool) : Nat.card (Quot (KeywordEquiv (n := 4) a)) = 12 := by
  rw [threeBitCount a 4 (by decide)]
  decide

end MetaMathlibExt.card_quot_keywordEquiv_eq_sum_mStepFibonacci
