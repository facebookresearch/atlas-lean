/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.DistinctConstantBlockPartitions

namespace MetaMathlibExt.ncard_distinctConstantBlockPartitions_eq_coloredCompositions

-- The empty multiset of blocks is counted.
example :
    {P : Multiset (Multiset ℕ) |
        P.Nodup ∧ (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧
          P.join.card = 0 ∧ ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard = 1 := by
  rw [ncard_distinctConstantBlockPartitions_eq_coloredCompositions]
  decide

-- A single element has a single possible block and color.
example :
    {P : Multiset (Multiset ℕ) |
        P.Nodup ∧ (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧
          P.join.card = 1 ∧ ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard = 1 := by
  rw [ncard_distinctConstantBlockPartitions_eq_coloredCompositions]
  rw [univ_eq_singleton_of_card_one (Composition.single 1 (by decide))
    (by rw [composition_card]; decide)]
  simp [Nat.Partition.distincts]

-- The common value may repeat across blocks of different sizes.
example :
    ({{1}, {1, 1}} : Multiset (Multiset ℕ)) ∈
      {P : Multiset (Multiset ℕ) |
        P.Nodup ∧ (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧
          P.join.card = 3 ∧ ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k} := by
  refine ⟨by decide, ?_, by decide, 1, by decide⟩
  intro b hb
  change b ∈ ({1} ::ₘ {{1, 1}} : Multiset (Multiset ℕ)) at hb
  simp only [Multiset.mem_cons, Multiset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact ⟨1, 1, by decide, rfl⟩
  · exact ⟨1, 2, by decide, rfl⟩

end MetaMathlibExt.ncard_distinctConstantBlockPartitions_eq_coloredCompositions
