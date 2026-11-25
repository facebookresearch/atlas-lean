/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.ColoredPartitionsRestrictedColors
import Mathlib.Order.Interval.Finset.Nat

open Finset

namespace MetaMathlibExt.coloredPartitions_differentParts_eq_restrictedColors

private abbrev Part := ℕ × ℕ
private def size (M : Multiset Part) : ℕ := (M.map Prod.fst).sum
private def valid (M : Multiset Part) : Prop := ∀ p ∈ M, 1 ≤ p.2 ∧ p.2 ≤ p.1

-- Independently enumerate partitions by choosing a first part and recursing on the remaining size.
-- The number of parts is bounded by the total size, so that size also suffices as fuel.
private def colored : ℕ → ℕ → Finset (Multiset Part)
  | _, 0 => {0}
  | 0, _ + 1 => ∅
  | fuel + 1, n + 1 =>
    (Icc 1 (n + 1)).biUnion fun m => (Icc 1 m).biUnion fun j =>
      (colored fuel (n + 1 - m)).image fun M => (m, j) ::ₘ M

private lemma valid_cons (p : Part) (M : Multiset Part) :
    valid (p ::ₘ M) ↔ (1 ≤ p.2 ∧ p.2 ≤ p.1) ∧ valid M := by
  simp [valid, Multiset.mem_cons, forall_eq_or_imp]

private lemma size_cons (p : Part) (M : Multiset Part) : size (p ::ₘ M) = p.1 + size M := by
  simp [size]

private lemma valid_size_zero (M : Multiset Part) : valid M ∧ size M = 0 ↔ M = 0 := by
  induction M using Multiset.induction_on with
  | empty => simp [valid, size]
  | cons p M _ =>
    simp only [valid_cons, size_cons, Multiset.cons_ne_zero, iff_false]
    rintro ⟨⟨⟨hj, hjm⟩, _⟩, hz⟩
    omega

private lemma mem_colored {fuel n : ℕ} (h : n ≤ fuel) (M : Multiset Part) :
    M ∈ colored fuel n ↔ valid M ∧ size M = n := by
  induction fuel generalizing n M with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    simpa [colored] using (valid_size_zero M).symm
  | succ fuel ih =>
    cases n with
    | zero => simpa [colored] using (valid_size_zero M).symm
    | succ n =>
      simp only [colored, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨m, ⟨hm, hmn⟩, j, ⟨hj, hjm⟩, T, hT, rfl⟩
        obtain ⟨hv, hs⟩ := (ih (n := n + 1 - m) (by omega) T).mp hT
        exact ⟨(valid_cons _ _).mpr ⟨⟨hj, hjm⟩, hv⟩, by rw [size_cons, hs]; omega⟩
      · rintro ⟨hv, hs⟩
        cases M using Multiset.induction_on with
        | empty => simp [size] at hs
        | cons p T _ =>
          obtain ⟨m, j⟩ := p
          obtain ⟨⟨hj, hjm⟩, hv⟩ := (valid_cons _ _).mp hv
          change 1 ≤ j at hj
          change j ≤ m at hjm
          rw [size_cons] at hs
          change m + size T = n + 1 at hs
          refine ⟨m, ⟨by omega, by omega⟩, j, ⟨hj, hjm⟩, T, ?_, rfl⟩
          exact (ih (n := n + 1 - m) (by omega) T).mpr ⟨hv, by omega⟩

private lemma ncard_colored (n : ℕ) (P : Multiset Part → Prop) [DecidablePred P] :
    {M | valid M ∧ size M = n ∧ P M}.ncard = ((colored n n).filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext M
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, mem_colored le_rfl]
  tauto

private def allowed (odd : Bool) (M : Multiset Part) : Prop :=
  ∀ p ∈ M, Even p.1 → if odd then ¬Even p.2 else Even p.2

private instance (odd : Bool) : DecidablePred (allowed odd) := fun M => by
  unfold allowed
  infer_instance

-- The empty partition is counted on all three sides.
example : {M | valid M ∧ size M = 0 ∧ Multiset.Nodup M}.ncard = 1 := by
  rw [ncard_colored]
  decide

example (odd : Bool) : {M | valid M ∧ size M = 0 ∧ allowed odd M}.ncard = 1 := by
  rw [ncard_colored]
  cases odd <;> decide

-- Corollary 4 includes the size-five example from the paper: all three counts are 16.
example : {M | valid M ∧ size M = 5 ∧ Multiset.Nodup M}.ncard = 16 := by
  rw [ncard_colored]
  decide

example : {M | valid M ∧ size M = 5 ∧ allowed true M}.ncard = 16 := by
  rw [ncard_colored]
  decide

example : {M | valid M ∧ size M = 5 ∧ allowed false M}.ncard = 16 := by
  rw [ncard_colored]
  decide

-- At size four, equal sizes with different colors are distinct, while equal pairs are not.
example :
    ([(2, 1), (2, 2)] : Multiset Part) ∈ (colored 4 4).filter Multiset.Nodup ∧
    ([(2, 1), (2, 1)] : Multiset Part) ∉ (colored 4 4).filter Multiset.Nodup := by
  decide

-- Each restriction allows repeated pairs of the permitted color, including the upper
-- endpoint `j = m` on the even-color side.
example :
    ([(2, 1), (2, 1)] : Multiset Part) ∈ (colored 4 4).filter (allowed true) ∧
    ([(2, 1), (2, 1)] : Multiset Part) ∉ (colored 4 4).filter (allowed false) ∧
    ([(2, 2), (2, 2)] : Multiset Part) ∈ (colored 4 4).filter (allowed false) ∧
    ([(2, 2), (2, 2)] : Multiset Part) ∉ (colored 4 4).filter (allowed true) := by
  decide

end MetaMathlibExt.coloredPartitions_differentParts_eq_restrictedColors
