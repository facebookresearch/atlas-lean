/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Binary PARTITION

The occurrence-sensitive PARTITION language from Garey and Johnson,
*Computers and Intractability* (1979). The definitions preserve the exact
`PartitionWanted` statement, including empty lists and zero entries.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition

/-- A partition instance: a list of natural numbers. -/
abbrev PartitionInstance := List ℕ

/-- A sublist summing to half the total. -/
def PartitionFeasible (i : PartitionInstance) : Prop :=
  ∃ s : List ℕ, s.Sublist i ∧ s.sum * 2 = i.sum

open Classical in
/-- PARTITION using the canonical binary list decoder; bad framing rejects. -/
noncomputable def partitionDec : ComplexityTheory.DecisionProblem := fun x =>
  match BitstringEncoding.bitDecode (α := PartitionInstance) x with
  | some i => decide (PartitionFeasible i)
  | none => false

/-- A canonical encoding has exactly the intended feasibility semantics. -/
@[simp] theorem partitionDec_bitEncode (as : List ℕ) :
    partitionDec (BitstringEncoding.bitEncode as) = true ↔
      PartitionFeasible as := by
  simp [partitionDec]

/-- The two padding entries in the SUBSET-SUM reduction.
No subtraction or range check is needed, even when `t > as.sum`. -/
def fromSubsetSum (as : List ℕ) (t : ℕ) : List ℕ :=
  as.sum :: (2 * t) :: as

private theorem complement_sum {s as : List ℕ} (h : s.Sublist as) :
    ∃ r : List ℕ, r.Sublist as ∧ s.sum + r.sum = as.sum := by
  induction h with
  | slnil => exact ⟨[], .slnil, rfl⟩
  | cons a _ ih =>
    obtain ⟨r, hr, he⟩ := ih
    exact ⟨a :: r, hr.cons_cons a, by simp only [List.sum_cons]; omega⟩
  | cons_cons a _ ih =>
    obtain ⟨r, hr, he⟩ := ih
    exact ⟨r, hr.cons a, by simp only [List.sum_cons]; omega⟩

/-- SUBSET-SUM reduces to PARTITION by adding two nonnegative entries. -/
theorem fromSubsetSum_feasible (as : List ℕ) (t : ℕ) :
    PartitionFeasible (fromSubsetSum as t) ↔
      ∃ s : List ℕ, s.Sublist as ∧ s.sum = t := by
  constructor
  · rintro ⟨s, hs, he⟩
    simp only [fromSubsetSum, List.sum_cons] at hs he
    rcases List.sublist_cons_iff.mp hs with hs | ⟨r, rfl, hr⟩
    · rcases List.sublist_cons_iff.mp hs with hs | ⟨r, rfl, hr⟩
      · have hb := hs.sum_le_sum (fun _ _ => Nat.zero_le _)
        exact ⟨[], List.nil_sublist _, by simp only [List.sum_nil]; omega⟩
      · obtain ⟨c, hc, hsum⟩ := complement_sum hr
        simp only [List.sum_cons] at he
        exact ⟨c, hc, by omega⟩
    · rcases List.sublist_cons_iff.mp hr with hr | ⟨q, rfl, hq⟩
      · simp only [List.sum_cons] at he
        exact ⟨r, hr, by omega⟩
      · simp only [List.sum_cons] at he
        exact ⟨[], List.nil_sublist _, by simp only [List.sum_nil]; omega⟩
  · rintro ⟨s, hs, he⟩
    refine ⟨as.sum :: s, (hs.cons (2 * t)).cons_cons as.sum, ?_⟩
    simp only [fromSubsetSum, List.sum_cons, he]
    omega

/-- Doubling each entry reduces PARTITION membership to SUBSET-SUM
without truncating division on odd totals. -/
theorem feasible_iff_doubled_sublist (as : List ℕ) :
    PartitionFeasible as ↔ ∃ s : List ℕ,
      s.Sublist (as.map (· * 2)) ∧ s.sum = as.sum := by
  have hsum (s : List ℕ) : (s.map (· * 2)).sum = s.sum * 2 := by
    simpa using List.sum_map_mul_right s id 2
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨s.map (· * 2), hs.map _, by rw [hsum, he]⟩
  · rintro ⟨s, hs, he⟩
    obtain ⟨r, hr, rfl⟩ := List.sublist_map_iff.mp hs
    exact ⟨r, hr, by rwa [hsum] at he⟩

end MetaMathlibExt.Complexity.NPComplete.Partition
