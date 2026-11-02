/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
replace the source-specific partition-count alias with canonical cardinalities, narrow imports,
and add importing-client tests.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Counting integer partitions

This file gives a part-removal bijection and consequences for the number of integer partitions.
The proofs are adapted from `eth/proof/rates/ClauseBound/Part/Rec.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
-/

@[expose] public section

namespace Nat.Partition

open Finset

/-- Removing `k` copies of the positive part `v` gives a bijection from partitions of `E`
containing at least `k` copies of `v` to partitions of `E - k * v`. -/
theorem card_count_ge {E v k : ℕ} (hv : 1 ≤ v) (hkv : k * v ≤ E) :
    Fintype.card {p : Partition E // k ≤ p.parts.count v} =
      Fintype.card (Partition (E - k * v)) := by
  classical
  have hsum : (Multiset.replicate k v).sum = k * v := by
    rw [Multiset.sum_replicate, smul_eq_mul]
  let e : {p : Partition E // k ≤ p.parts.count v} ≃ Partition (E - k * v) :=
    { toFun := fun p =>
        ⟨p.1.parts - Multiset.replicate k v,
          fun hi => p.1.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi),
          by
            have hle : Multiset.replicate k v ≤ p.1.parts :=
              Multiset.le_count_iff_replicate_le.mp p.2
            have hsum' := congrArg Multiset.sum (Multiset.sub_add_cancel hle)
            rw [Multiset.sum_add, hsum, p.1.parts_sum] at hsum'
            omega⟩
      invFun := fun p =>
        ⟨⟨p.parts + Multiset.replicate k v,
            fun hi => by
              rcases Multiset.mem_add.mp hi with hi | hi
              · exact p.parts_pos hi
              · rw [Multiset.eq_of_mem_replicate hi]
                exact hv,
            by
              rw [Multiset.sum_add, hsum, p.parts_sum]
              omega⟩,
          by simp⟩
      left_inv := fun p => by
        apply Subtype.ext
        exact Partition.ext
          (Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.mp p.2))
      right_inv := fun p => Partition.ext Multiset.add_sub_cancel_right }
  exact Fintype.card_congr e

/-- The number of integer partitions is monotone in the integer being partitioned. -/
theorem card_monotone : Monotone fun E => Fintype.card (Partition E) := by
  intro E E' hEE'
  have hcount := card_count_ge (E := E') (v := 1) (k := E' - E) (by omega) (by omega)
  rw [show E' - (E' - E) * 1 = E by omega] at hcount
  change Fintype.card (Partition E) ≤ Fintype.card (Partition E')
  rw [← hcount]
  exact Fintype.card_subtype_le _

private theorem sum_count_mul_eq {E : ℕ} (p : Partition E) :
    ∑ v ∈ Icc 1 E, p.parts.count v * v = E := by
  have hsub : p.parts.toFinset ⊆ Icc 1 E := fun v hv =>
    mem_Icc.mpr ⟨p.parts_pos (Multiset.mem_toFinset.mp hv),
      p.le_of_mem_parts (Multiset.mem_toFinset.mp hv)⟩
  have hsum := Finset.sum_multiset_count_of_subset p.parts (Icc 1 E) hsub
  rw [p.parts_sum] at hsum
  simpa only [smul_eq_mul] using hsum.symm

private theorem card_filter_Icc_le_count {E : ℕ} (p : Partition E) {v : ℕ}
    (hv : v ∈ Icc 1 E) :
    ({k ∈ Icc 1 (E / v) | k ≤ p.parts.count v}).card = p.parts.count v := by
  have hle : p.parts.count v * v ≤ E :=
    (single_le_sum (f := fun w => p.parts.count w * w) (fun _ _ => Nat.zero_le _) hv).trans
      (sum_count_mul_eq p).le
  have hle' : p.parts.count v ≤ E / v :=
    (Nat.le_div_iff_mul_le (mem_Icc.mp hv).1).mpr hle
  have heq : {k ∈ Icc 1 (E / v) | k ≤ p.parts.count v} =
      Icc 1 (p.parts.count v) := by
    ext k
    simp only [mem_filter, mem_Icc]
    omega
  rw [heq, Nat.card_Icc, Nat.add_sub_cancel]

/-- A recurrence obtained by summing all parts of all partitions of `E`, first by partition
and then by part value and multiplicity threshold. -/
theorem mul_card_eq_sum (E : ℕ) :
    E * Fintype.card (Partition E) =
      ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v),
        v * Fintype.card (Partition (E - k * v)) := by
  calc
    E * Fintype.card (Partition E) = ∑ _p : Partition E, E := by
      rw [sum_const, card_univ, smul_eq_mul, mul_comm]
    _ = ∑ p : Partition E, ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v),
          if k ≤ p.parts.count v then v else 0 := by
      refine sum_congr rfl fun p _ => (sum_count_mul_eq p).symm.trans ?_
      refine sum_congr rfl fun v hv => ?_
      rw [← sum_filter, sum_const, smul_eq_mul, card_filter_Icc_le_count p hv]
    _ = ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), ∑ p : Partition E,
          if k ≤ p.parts.count v then v else 0 := by
      rw [sum_comm]
      exact sum_congr rfl fun v _ => sum_comm
    _ = ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v),
          v * Fintype.card (Partition (E - k * v)) := by
      refine sum_congr rfl fun v hv => sum_congr rfl fun k hk => ?_
      have hv1 : 1 ≤ v := (mem_Icc.mp hv).1
      rw [← sum_filter, sum_const, smul_eq_mul,
        ← Fintype.card_subtype (fun p : Partition E => k ≤ p.parts.count v),
        card_count_ge hv1 ((Nat.le_div_iff_mul_le hv1).mp (mem_Icc.mp hk).2), mul_comm]

end Nat.Partition
