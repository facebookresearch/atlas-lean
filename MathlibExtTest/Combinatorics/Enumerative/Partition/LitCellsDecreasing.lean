/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.LitCellsDecreasing

open MetaMathlibExt PowerSeries
open scoped PowerSeries.WithPiTopology

-- The second column fits exactly under the first column's light bound.
example : litCellsDecreasing (Nat.Partition.ofMultiset {2, 1}) = 2 := by
  have hp : (Nat.Partition.ofMultiset {2, 1}).parts = 2 ::ₘ ({1} : Multiset ℕ) := by
    rw [Nat.Partition.ofMultiset_parts, Multiset.filter_eq_self.mpr (by simp)]
    rfl
  rw [litCellsDecreasing, decreasingParts, hp, Multiset.sort_cons _ _ _ (by simp),
    Multiset.sort_singleton]
  decide +kernel

-- A second column of the same height as the first increases the statistic.
example : litCellsDecreasing (Nat.Partition.ofMultiset {2, 2}) = 3 := by
  have hp : (Nat.Partition.ofMultiset {2, 2}).parts = 2 ::ₘ ({2} : Multiset ℕ) := by
    rw [Nat.Partition.ofMultiset_parts, Multiset.filter_eq_self.mpr (by simp)]
    rfl
  rw [litCellsDecreasing, decreasingParts, hp, Multiset.sort_cons _ _ _ (by simp),
    Multiset.sort_singleton]
  decide +kernel

-- The first staircase allows just the empty partition and the partition (1).
example : trianglePartitionSeries 1 = 1 + X := by
  simp [trianglePartitionSeries, Finset.sum_range_succ, triangularQBinomial_zero_right,
    triangularQBinomial_recursion.2.1]

-- The empty partition and (1) do not contribute to the generating function.
example :
    let F : ℤ⟦X⟧ := ∑' r : ℕ, ((r + 2 : ℕ) : ℤ⟦X⟧) * X ^ (r + 2) *
      trianglePartitionSeries (r + 1)
    coeff 0 F = 0 ∧ coeff 1 F = 0 := by
  dsimp only
  rw [← litCellsDecreasing_firstColumn_generatingFunction]
  simp

-- The full series has zero constant term and includes the one-cell partition.
example :
    let L : ℤ⟦X⟧ := ∑' k : ℕ, ((mk fun n => (Fintype.card (Nat.Partition n) : ℤ)) -
      trianglePartitionSeries k)
    coeff 0 L = 0 ∧ coeff 1 L = 1 := by
  dsimp only
  rw [← litCellsDecreasing_generatingFunction]
  simp [litCellsDecreasing, decreasingParts]

private def p4 (l : List ℕ) (h : l.sum = 4 := by decide) : Nat.Partition 4 :=
  Nat.Partition.ofSums 4 l h

private def partitions4 : Finset (Nat.Partition 4) :=
  {p4 [4], p4 [3, 1], p4 [2, 2], p4 [2, 1, 1], p4 [1, 1, 1, 1]}

-- Enumerate sorted positive lists of sum four without reducing the partition Fintype instance.
private theorem sorted_sum_four (l : List ℕ) (hs : l.sum = 4) (hp : ∀ x ∈ l, 0 < x)
    (hd : l.Pairwise (· ≥ ·)) :
    l = [4] ∨ l = [3, 1] ∨ l = [2, 2] ∨ l = [2, 1, 1] ∨ l = [1, 1, 1, 1] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩
  · simp at hs
  · simp_all
  · have ha := hp a (by simp)
    have hb := hp b (by simp)
    have hab : b ≤ a := (List.pairwise_cons.mp hd).1 b (by simp)
    simp at hs ⊢
    omega
  · have ha := hp a (by simp)
    have hb := hp b (by simp)
    have hc := hp c (by simp)
    have hab : b ≤ a := (List.pairwise_cons.mp hd).1 b (by simp)
    have hbc : c ≤ b := (List.pairwise_cons.mp (List.pairwise_cons.mp hd).2).1 c (by simp)
    simp at hs ⊢
    omega
  · have ha := hp a (by simp)
    have hb := hp b (by simp)
    have hc := hp c (by simp)
    have hd' := hp d (by simp)
    simp at hs ⊢
    omega
  · simp only [List.sum_cons] at hs
    have ha := hp a (by simp)
    have hb := hp b (by simp)
    have hc := hp c (by simp)
    have hd' := hp d (by simp)
    have he := hp e (by simp)
    omega

private theorem parts_p4 (l : List ℕ) (h : l.sum = 4) (hp : ∀ x ∈ l, 0 < x) :
    (p4 l h).parts = (l : Multiset ℕ) := by
  change (l : Multiset ℕ).filter (· ≠ 0) = (l : Multiset ℕ)
  exact Multiset.filter_eq_self.mpr fun a ha => ne_of_gt (hp a (by simpa using ha))

private theorem univ_eq_partitions4 : (Finset.univ : Finset (Nat.Partition 4)) = partitions4 := by
  refine Finset.Subset.antisymm (fun p _ => ?_) (Finset.subset_univ _)
  let l := decreasingParts p
  have hparts : (l : Multiset ℕ) = p.parts := Multiset.sort_eq _ _
  have hs : l.sum = 4 := by rw [← Multiset.sum_coe, hparts, p.parts_sum]
  have hp (x : ℕ) (hx : x ∈ l) : 0 < x := p.parts_pos (by rw [← hparts]; simpa using hx)
  have hd : l.Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  have heq (a : List ℕ) (ha : a.sum = 4) (h : l = a) : p = p4 a ha := by
    apply Nat.Partition.ext
    rw [parts_p4 _ _ (h ▸ hp), ← hparts, h]
  simp only [partitions4, Finset.mem_insert, Finset.mem_singleton]
  rcases sorted_sum_four l hs hp hd with h | h | h | h | h
  · exact Or.inl (heq _ _ h)
  · exact Or.inr (Or.inl (heq _ _ h))
  · exact Or.inr (Or.inr (Or.inl (heq _ _ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (heq _ _ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (heq _ _ h))))

private theorem litCells_p4 (l : List ℕ) (h : l.sum = 4) (hp : ∀ x ∈ l, 0 < x)
    (hl : l.Pairwise (· ≥ ·)) :
    litCellsDecreasing (p4 l h) = (l.mapIdx fun i x => x + i).foldr max 0 := by
  have hsort : (l : Multiset ℕ).sort (· ≥ ·) = l := by
    apply List.Perm.eq_of_pairwise
    · exact fun _ _ _ _ hab hba => Nat.le_antisymm hba hab
    · exact Multiset.pairwise_sort _ _
    · exact hl
    · exact Quotient.exact (Multiset.sort_eq _ _)
  rw [litCellsDecreasing, decreasingParts, parts_p4 _ _ hp, hsort]

-- The five partitions of four contribute 4, 3, 3, 3, and 4 lit cells.
example :
    coeff 4 (∑' k : ℕ, ((mk fun n => (Fintype.card (Nat.Partition n) : ℤ)) -
      trianglePartitionSeries k)) = 17 := by
  rw [← litCellsDecreasing_generatingFunction, coeff_mk, univ_eq_partitions4]
  simp only [partitions4]
  repeat rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_singleton]
  rw [litCells_p4 _ _ (by decide) (by decide), litCells_p4 _ _ (by decide) (by decide),
    litCells_p4 _ _ (by decide) (by decide), litCells_p4 _ _ (by decide) (by decide),
    litCells_p4 _ _ (by decide) (by decide)]
  decide +kernel
