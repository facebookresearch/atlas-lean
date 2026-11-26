/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.Combinatorics.Enumerative.Partition.RegularPartitionsLK

namespace MetaMathlibExt.regularPartitionCount_two_prime_mod_two

example : regularPartitionCount 2 5 0 = 1 := by decide

-- The single-part partition of 5 is allowed for (2, 7) and excluded for (2, 5).
example : regularPartitionCount 2 5 5 < regularPartitionCount 2 7 5 := by
  unfold regularPartitionCount
  apply Finset.card_lt_card
  have hsub : (Finset.univ : Finset (Nat.Partition 5)).filter
      (fun part => ∀ i ∈ part.parts, ¬ 2 ∣ i ∧ ¬ 5 ∣ i) ⊆
      Finset.univ.filter (fun part => ∀ i ∈ part.parts, ¬ 2 ∣ i ∧ ¬ 7 ∣ i) := by
    intro part hpart
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpart ⊢
    intro i hi
    have hi_le := Nat.Partition.le_of_mem_parts hi
    exact ⟨(hpart i hi).1, fun hd =>
      (by omega : ¬ 7 ≤ i) (Nat.le_of_dvd (part.parts_pos hi) hd)⟩
  refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨Nat.Partition.indiscrete 5, ?_, ?_⟩ <;> simp

private lemma nonresidue_five_three : ¬ IsSquare ((24 * 3 + 1 : ℕ) : ZMod 5) := by
  change ¬ ∃ a : ZMod 5, (3 : ZMod 5) = a * a
  decide

example (n : ℕ) : regularPartitionCount 2 5 (5 * n + 3) ≡ 0 [MOD 2] :=
  regularPartitionCount_two_prime_mod_two (p := 5) (r := 3)
    (by decide) (by decide) nonresidue_five_three n

end MetaMathlibExt.regularPartitionCount_two_prime_mod_two
