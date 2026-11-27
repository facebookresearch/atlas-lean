/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.PentagonalRecurrenceParity

private def pentagonalSum (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
    Fintype.card (Nat.Partition (n - (k * (3 * k + 1) / 2).toNat))

example (n : ℕ) (hn : 0 < n) : Even (pentagonalSum n) :=
  MetaMathlibExt.partition_pentagonal_sum_even (n := n) (hn := hn)

-- At zero the empty partition contributes the only term, so positivity is necessary.
example : pentagonalSum 0 = 1 := by decide

private theorem card_partition_two : Fintype.card (Nat.Partition 2) = 2 := by
  let a := Nat.Partition.indiscrete 2
  let b := Nat.Partition.ofSums 2 ({1, 1} : Multiset ℕ) (by decide)
  have ha : a.parts = {2} := by simp [a]
  have hb : b.parts = {1, 1} := rfl
  have hab : a ≠ b := by
    intro h
    have hparts := congrArg Nat.Partition.parts h
    rw [ha, hb] at hparts
    exact (by decide : ({2} : Multiset ℕ) ≠ {1, 1}) hparts
  have huniv : (Finset.univ : Finset (Nat.Partition 2)) = {a, b} := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases h : 2 ∈ p.parts
    · left
      let e : {q : Nat.Partition 2 // 2 ∈ q.parts} ≃ Nat.Partition 0 :=
        Nat.Partition.partitionWithPartEquiv (by decide) le_rfl
      exact congrArg Subtype.val (e.injective
        (Subsingleton.elim (e ⟨p, h⟩) (e ⟨a, by simp [ha]⟩)))
    · right
      have hrepl : p.parts = Multiset.replicate p.parts.card 1 := by
        refine Multiset.eq_replicate_card.mpr fun i hi => ?_
        have hle := (Multiset.le_sum_of_mem hi).trans_eq p.parts_sum
        have hne : i ≠ 2 := fun hi2 => h (hi2 ▸ hi)
        have hpos := p.parts_pos hi
        omega
      have hc : p.parts.card = 2 := by
        simpa using (congrArg Multiset.sum hrepl.symm).trans p.parts_sum
      exact Nat.Partition.ext (by rw [hrepl, hc, hb]; rfl)
  rw [Fintype.card, huniv, Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]

-- At one the indices are `-1, 0`; at two the index `1` also contributes.
example : pentagonalSum 1 = 2 := by decide
example : pentagonalSum 2 = 4 := by
  have hindices : ((Finset.Icc (-((2 : ℕ) : ℤ)) (2 : ℕ)).filter
      (fun k : ℤ => k * (3 * k + 1) / 2 ≤ ((2 : ℕ) : ℤ))) = {-1, 0, 1} := by decide
  unfold pentagonalSum
  rw [hindices, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  change Fintype.card (Nat.Partition 1) +
    (Fintype.card (Nat.Partition 2) + Fintype.card (Nat.Partition 0)) = 4
  rw [card_partition_two, Fintype.card_unique, Fintype.card_unique]
