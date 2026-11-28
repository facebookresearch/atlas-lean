/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ShakovTwoRegular

open MathlibExt.NumberTheory.ShakovTwoRegularWanted

-- The dummy term is zero, and index one is the only positive index in the zero fiber.
example : shakovSeq 0 = 0 := by norm_num [shakovSeq.eq_1]

example (n : ℕ) : (1 ≤ n ∧ shakovSeq n = 0) ↔ n = 1 := by
  obtain ⟨_, F, hF, hcard⟩ := fiber_card 0
  have hsubset : ({1} : Finset ℕ) ⊆ F :=
    Finset.singleton_subset_iff.mpr ((hF 1).2 (by norm_num [shakovSeq.eq_2]))
  have heq := Finset.eq_of_subset_of_card_le hsubset (by rw [hcard]; decide)
  simpa [← heq] using (hF n).symm

-- The four divisors of ten give these four indices, spanning two levels of the tree.
example (n : ℕ) : (1 ≤ n ∧ shakovSeq n = 3) ↔ n ∈ ({5, 6, 8, 15} : Finset ℕ) := by
  obtain ⟨_, F, hF, hcard⟩ := fiber_card 3
  have hsubset : ({5, 6, 8, 15} : Finset ℕ) ⊆ F := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;>
      exact (hF _).2 (by
        norm_num [shakovSeq.eq_2, shakovSeq.eq_3, shakovSeq.eq_4, shakovSeq.eq_5])
  have heq := Finset.eq_of_subset_of_card_le hsubset (by rw [hcard]; decide)
  rw [heq]
  exact (hF n).symm

-- Directly evaluate both orders of the child pair beyond the initial triple.
example : (shakovA 4, shakovA 5, shakovA 6, shakovA 7) = (4, 5, 11, 10) := by decide

example : shakovSeq (shakovA 6).toNat = 5 ∧ shakovSeq (shakovA 7).toNat = 8 := by
  norm_num [shakovA, shakovSeq.eq_2, shakovSeq.eq_3, shakovSeq.eq_4, shakovSeq.eq_5]

-- Exercise the proved API at the first allowed index and after several pair advances.
example : shakovSeq (shakovA 1).toNat = 0 := by
  simpa using shakovSeq_shakovA 1 (by decide)

example : shakovSeq (shakovA 9).toNat = 21 :=
  (shakovSeq_shakovA 9 (by decide)).trans (by decide)

-- The first positive fiber has just its two endpoints, since 1² + 1 is prime.
example : {m : ℕ | shakovSeq m = 1} = {2, 3} :=
  (prime_iff_fiber 1 (by decide)).mp (by decide)

-- The composite value 3² + 1 gives a fiber larger than its endpoint pair.
example : {m : ℕ | shakovSeq m = 3} ≠ {8, 15} :=
  mt (prime_iff_fiber 3 (by decide)).mpr (by decide)
