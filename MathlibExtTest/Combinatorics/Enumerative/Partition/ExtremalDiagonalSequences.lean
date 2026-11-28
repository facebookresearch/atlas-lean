/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.ExtremalDiagonalSequences

namespace MetaMathlibExt

-- The empty partition gives zero even at indices beyond the length of the normal form.
example (s : ℕ → ℕ) (k : ℕ) : diagonalSequence ↑(diagonalMaxPartition 0 s) k = 0 := by
  obtain ⟨h, hmin, _⟩ := diagonalSequence_max_eq_min_and_multiset 0 s
  rw [h, hmin]
  cases k <;> rfl

-- The four-row example skips the block of threes and repeats the largest height.
example :
    diagonalSequence ↑([8, 6, 4, 3] : List ℕ) =
      diagonalOfList [1, 2, 3, 4, 4, 4, 2, 1] ∧
    diagonalSequence ↑([4, 4, 4, 3, 2, 2, 1, 1] : List ℕ) =
      diagonalOfList [1, 2, 3, 4, 4, 4, 2, 1] ∧
    ([1, 2, 3, 4, 4, 4, 2, 1] : Multiset ℕ) = ↑([4, 4, 4, 3, 2, 2, 1, 1] : List ℕ) := by
  obtain ⟨h, hmin, hparts⟩ :=
    diagonalSequence_max_eq_min_and_multiset 4 (fun k => [0, 1, 1, 0, 2].getD k 0)
  simpa only [diagonalMaxPartition_four_example, diagonalMinPartition_four_example,
    diagonalNormalForm_four_example] using And.intro (h.trans hmin) (And.intro hmin hparts)

-- The class of `(3, 1)` is `{(3, 1), (2, 2), (2, 1, 1)}`: a single factor `C(3, 2)`.
example : (diagonalClass (Nat.Partition.ofMultiset {3, 1})).card = 3 := by
  rw [card_diagonalClass_eq_prod_choose _ 2 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- The paper's running example `(7, 7, 4, 1, 1, 1)` has 36 partitions in its class; the zero
-- drops after the staircase give factors `1` and `3`.
example : (diagonalClass (Nat.Partition.ofMultiset {7, 7, 4, 1, 1, 1})).card = 36 := by
  rw [card_diagonalClass_eq_prod_choose _ 4 8 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- A staircase is alone in its class: `q = L` and the product is empty.
example : (diagonalClass (Nat.Partition.ofMultiset {3, 2, 1})).card = 1 := by
  rw [card_diagonalClass_eq_prod_choose _ 3 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  rfl

-- The single part `1` is the smallest staircase, with `q = L = 1`.
example : (diagonalClass (Nat.Partition.ofMultiset {1})).card = 1 := by
  rw [card_diagonalClass_eq_prod_choose _ 1 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  rfl

-- The row `(3)` shares its class only with the column `(1, 1, 1)`.
example : (diagonalClass (Nat.Partition.ofMultiset {3})).card = 2 := by
  rw [card_diagonalClass_eq_prod_choose _ 1 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- The class of `(4, 3, 2)` has four elements, the last case of the paper's Corollary 7 (4).
example : (diagonalClass (Nat.Partition.ofMultiset {4, 3, 2})).card = 4 := by
  rw [card_diagonalClass_eq_prod_choose _ 3 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- The class of `(3, 1)` has two partitions with two parts: `(3, 1)` and `(2, 2)`.
example : ((diagonalClass (Nat.Partition.ofMultiset {3, 1})).filter
    fun β => β.parts.card = 2).card = 2 := by
  rw [card_diagonalClass_filter_card_parts_eq_q _ 2 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- The paper's running example tests several levels, including two initial zero drops.
example : ((diagonalClass (Nat.Partition.ofMultiset {7, 7, 4, 1, 1, 1})).filter
    fun β => β.parts.card = 4).card = 6 := by
  rw [card_diagonalClass_filter_card_parts_eq_q _ 4 8 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- For `(4, 1)`, the drops are `1, 0, 1`: the missing middle letter gives factors of `1`.
example : ((diagonalClass (Nat.Partition.ofMultiset {4, 1})).filter
    fun β => β.parts.card = 2).card = 1 := by
  rw [card_diagonalClass_filter_card_parts_eq_q _ 2 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- A staircase has `q = L`, so the product is empty.
example : ((diagonalClass (Nat.Partition.ofMultiset {3, 2, 1})).filter
    fun β => β.parts.card = 3).card = 1 := by
  rw [card_diagonalClass_filter_card_parts_eq_q _ 3 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  rfl

-- At the minimum height, only the four extra copies of the peak are capped.
example :
    (diagonalClassOf 5 (diagonalOfList [1, 1, 1, 1, 1])).card =
      (diagonalClassOf 3 (diagonalOfList [1, 1, 1])).card :=
  card_diagonalClassOf_min_two 1 (by decide) (fun _ => 4)

-- Cap both the peak and the terminal height while retaining the singleton and the skipped level.
example :
    (diagonalClassOf 28 (diagonalOfList [1, 2, 3, 4, 4, 4, 4, 2, 1, 1, 1, 1])).card =
      (diagonalClassOf 22 (diagonalOfList [1, 2, 3, 4, 4, 4, 2, 1, 1])).card :=
  card_diagonalClassOf_min_two 4 (by decide) (fun k => [0, 4, 1, 0, 3].getD k 0)

private def rowTwo : Nat.Partition 2 := Nat.Partition.ofMultiset {2}
private def colTwo : Nat.Partition 2 := Nat.Partition.ofMultiset {1, 1}

-- Enumerate the entire class of the row of length two without using a counting formula.
private theorem class_rowTwo : diagonalClass rowTwo = {rowTwo, colTwo} := by
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro _
    by_cases h : 2 ∈ p.parts
    · obtain ⟨m, hm⟩ := Multiset.exists_cons_of_mem h
      have hsum := p.parts_sum
      rw [hm, Multiset.sum_cons] at hsum
      have hz : m = 0 := Multiset.eq_zero_of_forall_notMem fun a ha =>
        (p.parts_pos (hm ▸ Multiset.mem_cons_of_mem ha)).ne'
          (Multiset.sum_eq_zero_iff.mp (by omega : m.sum = 0) a ha)
      exact Or.inl (Nat.Partition.ext (by rw [hm, hz]; rfl))
    · have hr := (Multiset.eq_replicate_card (s := p.parts) (a := 1)).mpr fun a ha => by
        have hpos := p.parts_pos ha
        have hle := Nat.Partition.le_of_mem_parts ha
        have hne : a ≠ 2 := fun he => h (he ▸ ha)
        omega
      have hc : p.parts.card = 2 := by
        simpa [Multiset.sum_replicate, p.parts_sum] using (congrArg Multiset.sum hr).symm
      exact Or.inr (Nat.Partition.ext (by rw [hr, hc]; rfl))
  · rintro (rfl | rfl)
    · exact mem_diagonalClass_self _
    · apply mem_diagonalClass_iff.mpr
      rw [show rowTwo.parts = ↑(diagonalMaxPartition 1 (fun _ => 1)) by decide +kernel,
        show colTwo.parts = ↑(diagonalMinPartition 1 (fun _ => 1)) by decide +kernel]
      exact (diagonalSequence_max_eq_min_and_multiset 1 (fun _ => 1)).1.symm

-- For q = 1 and s₁ = 1, the two partitions have one and two parts; the drop product is two.
example : ((diagonalClass rowTwo).filter fun β => β.parts.card = 1).card = 1 ∧
    (diagonalClass rowTwo).card = 2 ∧
    (diagonalClass rowTwo).card = ∏ i ∈ Finset.Icc 1 2,
      (diagonalSequence rowTwo.parts i - diagonalSequence rowTwo.parts (i + 1) + 1) := by
  rw [class_rowTwo]
  decide +kernel

private def fourOne : Nat.Partition 5 := Nat.Partition.ofMultiset {4, 1}

-- With q = 2, s₁ = 2 and s₂ = 0, the only other two-part candidate is (3, 2).
-- It has two cells on diagonal 3, whereas (4, 1) has one.
example : (diagonalClass fourOne).filter (fun β => β.parts.card = 2) = {fourOne} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨Finset.mem_filter.mpr ⟨mem_diagonalClass_self _, by decide⟩, ?_⟩
  intro p hp
  obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
  obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hc
  have ha := p.parts_pos (show a ∈ p.parts by simp [hparts])
  have hb := p.parts_pos (show b ∈ p.parts by simp [hparts])
  have hs : a + b = 5 := by simpa [hparts, Multiset.insert_eq_cons] using p.parts_sum
  have hd := congrFun (mem_diagonalClass_iff.mp hp) 3
  rw [hparts] at hd
  have hc : (a = 4 ∧ b = 1) ∨ (a = 1 ∧ b = 4) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 3) := by
    omega
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Nat.Partition.ext hparts
  · exact Nat.Partition.ext (hparts.trans (by decide +kernel))
  · exact False.elim ((by decide +kernel : diagonalSequence {3, 2} 3 ≠ 1) hd)
  · exact False.elim ((by decide +kernel : diagonalSequence {2, 3} 3 ≠ 1) hd)

-- At q = L = 1 there is just the partition (1), which has exactly one part.
example : ((diagonalClass (Nat.Partition.indiscrete 1)).filter fun β => β.parts.card = 1).card =
    1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨Nat.Partition.indiscrete 1, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨mem_diagonalClass_self _, by decide⟩
  · intro p _
    exact Subsingleton.elim p _

-- Client of both counts at the minimum allowed lower multiplicity and with one extra peak.
example :
    let p : Nat.Partition 7 := Nat.Partition.ofMultiset {5, 2}
    ((diagonalClass p).filter fun β => β.parts.card = 2).card = 1 ∧ (diagonalClass p).card = 4 := by
  let p : Nat.Partition 7 := Nat.Partition.ofMultiset {5, 2}
  let s (k : ℕ) := [0, 2, 1].getD k 0
  have hp : p.parts = ↑(diagonalMaxPartition 2 s) := by dsimp only [p, s]; decide +kernel
  have hs : ∀ i ∈ Finset.Ico 1 2, 2 ≤ s i := by dsimp only [s]; decide
  have hsq : 1 ≤ s 2 := by dsimp only [s]; decide
  have hprod : (∏ i ∈ Finset.Icc 2 (2 + ∑ j ∈ Finset.Icc 1 2, s j),
      (diagonalSequence p.parts i - diagonalSequence p.parts (i + 1) + 1)) = 4 := by
    dsimp only [p, s]
    decide +kernel
  have hd : diagonalSequence p.parts = diagonalOfList (diagonalNormalForm 2 s) := by
    rw [hp]
    have h := diagonalSequence_max_eq_min_and_multiset 2 s
    exact h.1.trans h.2.1
  obtain ⟨hmin, hall⟩ := card_diagonalClass_of_two_le_s p 2 (by decide) s hd hs
  exact ⟨hmin, (hall hsq).trans hprod⟩

end MetaMathlibExt
