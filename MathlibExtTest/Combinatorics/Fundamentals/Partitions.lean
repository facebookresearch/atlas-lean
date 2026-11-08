/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import MathlibExt.Combinatorics.Fundamentals.Partitions
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace MathlibExtTest.Combinatorics.Fundamentals.Partitions

open MetaMathlibExt

-- Combinatorics 27: Weak Composition

theorem weakComposition_one_one :
    Nonempty (WeakComposition 1 1) := by
  exact ⟨⟨fun _ => 1, by simp⟩⟩

-- Combinatorics 28: Ordered Set Partition

theorem setComposition_two_singletons :
    Nonempty
      (SetComposition
        (Finset.univ : Finset (Fin 2)) 2) := by
  exact ⟨⟨fun i => {i}, by simp⟩⟩

-- Combinatorics 444: Conjugate Partition


theorem List.partitionConjugate_example :
    [4, 2, 2, 1].partitionConjugate = [4, 3, 1, 1] ∧
      [4, 3, 1, 1].partitionConjugate = [4, 2, 2, 1] := by
  decide

-- Combinatorics 445: Self-Conjugate Partition


theorem List.isSelfConjugate_example :
    List.IsSelfConjugate [3, 1, 1] ∧
      ¬ List.IsSelfConjugate [3, 1] := by
  unfold List.IsSelfConjugate
  refine ⟨by decide, by decide⟩

-- Combinatorics 452: Partitions in a Box


theorem Nat.partitionsInBox_sanity :
    (∀ j k : ℕ, Nat.partitionsInBox j k 0 = 1) ∧
      0 < Nat.partitionsInBox 1 1 1 := by
  constructor
  · intro j k
    rw [Nat.partitionsInBox, Finset.filter_true_of_mem,
      Finset.card_univ, Fintype.card_unique]
    intro p _
    exact ⟨by simp, by simp⟩
  · rw [Nat.partitionsInBox]
    refine Finset.card_pos.2 ⟨⟨{1}, ?_, ?_⟩, ?_⟩
    · intro i hi; simp at hi; omega
    · simp
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
      · simp
      · intro x hx; simp at hx; omega

-- Combinatorics 460: V-Partition


theorem Nat.VPartition.exists_ne_two_and_eq_zero :
    (∃ p q : Nat.VPartition 2, p ≠ q) ∧
      ∀ p q : Nat.VPartition 0, p = q := by
  have key : ∀ (c : ℕ) (l r : Multiset ℕ),
      (∀ x ∈ l, 0 < x) → (∀ x ∈ r, 0 < x) →
      c + l.sum + r.sum = 0 →
      c = 0 ∧ l = 0 ∧ r = 0 := by
    intro c l r hl hr hw
    have hls : l.sum = 0 := by omega
    have hrs : r.sum = 0 := by omega
    have h1 := Multiset.sum_eq_zero_iff.mp hls
    have h2 := Multiset.sum_eq_zero_iff.mp hrs
    refine ⟨by omega, ?_, ?_⟩
    · refine Multiset.eq_zero_of_forall_notMem ?_
      exact fun x hx => (hl x hx).ne' (h1 x hx)
    · refine Multiset.eq_zero_of_forall_notMem ?_
      exact fun x hx => (hr x hx).ne' (h2 x hx)
  constructor
  · exact ⟨⟨2, 0, 0, by simp, by simp, by simp, by simp,
      by simp⟩,
      ⟨1, {1}, 0, by simp, by simp, by simp, by simp,
        by simp⟩,
      fun h => by
        simpa using congrArg Nat.VPartition.corner h⟩
  · rintro ⟨c, l, r, a, b, d, e, f⟩
      ⟨c2, l2, r2, a2, b2, d2, e2, f2⟩
    obtain ⟨rfl, rfl, rfl⟩ := key c l r a b f
    obtain ⟨rfl, rfl, rfl⟩ := key c2 l2 r2 a2 b2 f2
    rfl

-- Combinatorics 461: Unimodal Sequence


theorem List.isUnimodal_plateau_and_not :
    List.IsUnimodal [1, 3, 3, 2] ∧
      ¬ List.IsUnimodal [2, 1, 3] ∧
        ¬ List.IsUnimodal [] := by
  unfold List.IsUnimodal
  decide

-- Combinatorics 489: Dominance Order


theorem Nat.Partition.dominates_six :
    let a : Nat.Partition 6 := ⟨{3, 1, 1, 1}, by decide, rfl⟩
    let b : Nat.Partition 6 := ⟨{2, 2, 2}, by decide, rfl⟩
    let c : Nat.Partition 6 := ⟨{2, 1, 1, 1, 1}, by decide, rfl⟩
    a.Dominates c ∧ ¬ a.Dominates b ∧ ¬ b.Dominates a := by
  intro a b c
  have ha : a.parts.sort (· ≥ ·) = [3, 1, 1, 1] :=
    List.mergeSort_of_pairwise (by decide)
  have hb : b.parts.sort (· ≥ ·) = [2, 2, 2] :=
    List.mergeSort_of_pairwise (by decide)
  have hc : c.parts.sort (· ≥ ·) = [2, 1, 1, 1, 1] :=
    List.mergeSort_of_pairwise (by decide)
  unfold Nat.Partition.Dominates
  rw [ha, hb, hc]
  refine ⟨fun i => ?_, fun h => absurd (h 3) (by decide),
    fun h => absurd (h 1) (by decide)⟩
  rcases Nat.lt_or_ge i 5 with hi | hi
  · interval_cases i <;> decide
  · rw [List.take_of_length_le (by simp; omega),
      List.take_of_length_le (by simp; omega)]
    decide

end MathlibExtTest.Combinatorics.Fundamentals.Partitions

end
