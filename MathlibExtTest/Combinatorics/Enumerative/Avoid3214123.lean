/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Avoid3214123
import Mathlib.Data.Fintype.Perm

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

-- Kernel evaluation exhaustively scans the permutations and index maps of `Fin 4`.
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def avoiders (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123

private def countsByMaxSlot (n : ℕ) : List ℕ :=
  (List.finRange (n + 1)).reverse.map fun p =>
    ((avoiders (n + 1)).filter fun σ => σ p = Fin.last n).card

-- Enumerate permutations directly, without the insertion recurrence.
example : [((avoiders 1).card), (avoiders 2).card, (avoiders 3).card, (avoiders 4).card] =
    [1, 2, 5, 13] := by decide

-- Counts from the last slot to the first, including the impossible fourth slot.
example : countsByMaxSlot 2 = [2, 2, 1] := by decide
example : countsByMaxSlot 3 = [5, 5, 3, 0] := by decide

-- Compare the generic pattern scan to direct searches for triples and quadruples.
example : ∀ σ : Equiv.Perm (Fin 4),
    (HasPattern σ pat321 ↔ ∃ a b c, a < b ∧ b < c ∧ σ c < σ b ∧ σ b < σ a) ∧
    (HasPattern σ pat4123 ↔
      ∃ a b c d, a < b ∧ b < c ∧ c < d ∧ σ b < σ c ∧ σ c < σ d ∧ σ d < σ a) := by
  decide

-- Independently exhibit an embedding for a nonconsecutive occurrence of 321.
example : ∃ e : Fin 3 ↪o Fin 4, ∀ i j,
    (Equiv.swap (0 : Fin 4) 3) (e i) < (Equiv.swap (0 : Fin 4) 3) (e j) ↔
      pat321 i < pat321 j := by
  let e : Fin 3 ↪o Fin 4 := OrderEmbedding.ofStrictMono ![0, 2, 3]
    (Fin.strictMono_iff_lt_succ.2 (by decide))
  exact ⟨e, by decide⟩

-- A client of the theorem can use the original statement without a conversion lemma.
example : Nat.card {σ : Equiv.Perm (Fin 4) // ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123} =
    Nat.fib 7 :=
  card_avoid_321_4123 4 (by decide)
