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

namespace MetaMathlibExt.ncard_constantBlockPartitions_eq_doubleCompositions

-- The empty multiset of blocks is counted.
example :
    {P : Multiset (Multiset ℕ) |
        (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧ P.join.card = 0 ∧
          ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard = 1 := by
  rw [ncard_constantBlockPartitions_eq_doubleCompositions]
  decide

private def compositionsTwo : Finset (Composition 2) :=
  {⟨[2], by simp, rfl⟩, ⟨[1, 1], by simp, rfl⟩}

private def compositionsThree : Finset (Composition 3) :=
  {⟨[3], by simp, rfl⟩, ⟨[1, 2], by simp, rfl⟩,
    ⟨[2, 1], by simp, rfl⟩, ⟨[1, 1, 1], by simp, rfl⟩}

private lemma univ_compositions {n : ℕ} (cs : Finset (Composition n))
    (h : cs.card = 2 ^ (n - 1)) : Finset.univ = cs := by
  symm
  refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
  rw [Finset.card_univ, composition_card, h]

private lemma partition_card {n : ℕ} (cs : Finset (Composition n)) (h : cs.card = 2 ^ (n - 1)) :
    Fintype.card (Nat.Partition n) = (cs.image (Nat.Partition.ofComposition n)).card := by
  rw [← univ_compositions cs h]
  rfl

-- The eight partitions in the paper's example at n = 3.
example :
    {P : Multiset (Multiset ℕ) |
        (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧ P.join.card = 3 ∧
          ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard = 8 := by
  rw [ncard_constantBlockPartitions_eq_doubleCompositions]
  have h2 : Fintype.card (Nat.Partition 2) = 2 :=
    (partition_card compositionsTwo (by decide)).trans (by decide)
  have h3 : Fintype.card (Nat.Partition 3) = 3 := by
    rw [partition_card compositionsThree (by decide)]
    -- The compositions [1, 2] and [2, 1] give the same partition.
    have hperm : Nat.Partition.ofComposition 3 ⟨[1, 2], by simp, rfl⟩ =
        Nat.Partition.ofComposition 3 ⟨[2, 1], by simp, rfl⟩ :=
      Nat.Partition.ext (Quot.sound (List.Perm.swap 2 1 []))
    simp only [compositionsThree, Finset.image_insert, Finset.image_singleton, hperm,
      Finset.insert_idem]
    decide
  rw [univ_compositions compositionsThree (by decide)]
  simp [compositionsThree, Finset.sum_insert, Composition.ext_iff, h2, h3]

-- In particular, three identical blocks are admissible.
example :
    ({{1}, {1}, {1}} : Multiset (Multiset ℕ)) ∈
      {P : Multiset (Multiset ℕ) |
        (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧ P.join.card = 3 ∧
          ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k} := by
  refine ⟨?_, by decide, 1, by decide⟩
  intro b hb
  have h : b = {1} := by
    change b ∈ ({1} ::ₘ {1} ::ₘ {{1}} : Multiset (Multiset ℕ)) at hb
    simpa only [Multiset.mem_cons, Multiset.mem_singleton, or_self] using hb
  subst b
  exact ⟨1, 1, by decide, rfl⟩

end MetaMathlibExt.ncard_constantBlockPartitions_eq_doubleCompositions
