/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `306b05307ce5e07e232dc0c0f350c714e8df4107`.
Original formalization by Tsutomu Okano (@toskua) with Avocado (internal agent
identity); ported with permission.
-/

module

public import Mathlib.Order.Partition.Finpartition

/-!
# Noncrossing partitions of `Fin n`

This file defines crossings by four interleaved points and bundles
noncrossing finite partitions with the refinement order inherited from
`Finpartition`.
-/

@[expose] public section

open Finpartition Finset

namespace NoncrossingPartition

/-- Set partitions of `Fin n` as `Finpartition` of `Finset.univ`. -/
abbrev SetPartition (n : ℕ) :=
  Finpartition (Finset.univ : Finset (Fin n))

/-- `P` has a crossing: there are `a < b < c < d` with `a,c` in one block,
`b,d` in another distinct block.  Blocks are compared via `P.part`. -/
def HasCrossing {n : ℕ} (P : SetPartition n) : Prop :=
  ∃ a b c d : Fin n,
    a < b ∧ b < c ∧ c < d ∧
      P.part a = P.part c ∧ P.part b = P.part d ∧ P.part a ≠ P.part b

/-- A partition of `Fin n` is noncrossing iff it has no crossing. -/
def IsNoncrossing {n : ℕ} (P : SetPartition n) : Prop :=
  ¬ HasCrossing P

instance {n : ℕ} (P : SetPartition n) : Decidable (HasCrossing P) := by
  unfold HasCrossing
  infer_instance

instance {n : ℕ} (P : SetPartition n) : Decidable (IsNoncrossing P) := by
  unfold IsNoncrossing
  infer_instance

end NoncrossingPartition

/-- Noncrossing partitions of `Fin n`. -/
def NoncrossingPartition (n : ℕ) :=
  { P : NoncrossingPartition.SetPartition n // NoncrossingPartition.IsNoncrossing P }

namespace NoncrossingPartition

instance (n : ℕ) : DecidableEq (_root_.NoncrossingPartition n) :=
  Subtype.instDecidableEq

instance (n : ℕ) : Fintype (_root_.NoncrossingPartition n) :=
  Subtype.fintype _

instance (n : ℕ) : PartialOrder (_root_.NoncrossingPartition n) :=
  PartialOrder.lift (fun P => P.val) Subtype.coe_injective

/-- Block accessor for noncrossing partitions. -/
def block {n : ℕ} (P : _root_.NoncrossingPartition n) (a : Fin n) : Finset (Fin n) :=
  P.val.part a

@[simp]
theorem part_mem_parts {n : ℕ} (P : SetPartition n) (a : Fin n) :
    P.part a ∈ P.parts := by
  rw [Finpartition.part_mem]
  exact mem_univ a

@[simp]
theorem mem_part_self {n : ℕ} (P : SetPartition n) (a : Fin n) :
    a ∈ P.part a := by
  rw [Finpartition.mem_part_self]
  exact mem_univ a

@[simp]
theorem mem_block_self {n : ℕ} (P : _root_.NoncrossingPartition n) (a : Fin n) :
    a ∈ block P a :=
  mem_part_self P.val a

@[simp]
theorem block_mem_parts {n : ℕ} (P : _root_.NoncrossingPartition n) (a : Fin n) :
    block P a ∈ P.val.parts :=
  part_mem_parts P.val a

@[ext]
theorem ext {n : ℕ} {P Q : _root_.NoncrossingPartition n}
    (h : P.val = Q.val) : P = Q :=
  Subtype.ext h

/-- Every partition of `Fin n` is noncrossing when `n ≤ 3`. -/
theorem isNoncrossing_of_le_three {n : ℕ} (hn : n ≤ 3) (P : SetPartition n) :
    IsNoncrossing P := by
  intro hcross
  obtain ⟨a, b, c, d, hab, hbc, hcd, _, _, _⟩ := hcross
  have hab' : (a : ℕ) < (b : ℕ) := hab
  have hbc' : (b : ℕ) < (c : ℕ) := hbc
  have hcd' : (c : ℕ) < (d : ℕ) := hcd
  have hab_le : (a : ℕ) + 1 ≤ (b : ℕ) := Nat.succ_le_of_lt hab'
  have hbc_le : (b : ℕ) + 1 ≤ (c : ℕ) := Nat.succ_le_of_lt hbc'
  have hcd_le : (c : ℕ) + 1 ≤ (d : ℕ) := Nat.succ_le_of_lt hcd'
  have h_ac : (a : ℕ) + 2 ≤ (c : ℕ) := by
    calc (a : ℕ) + 2 = (a : ℕ) + 1 + 1 := by omega
      _ ≤ (b : ℕ) + 1 := Nat.add_le_add_right hab_le 1
      _ ≤ (c : ℕ) := hbc_le
  have h_ad : (a : ℕ) + 3 ≤ (d : ℕ) := by
    calc (a : ℕ) + 3 = ((a : ℕ) + 2) + 1 := by omega
      _ ≤ (c : ℕ) + 1 := Nat.add_le_add_right h_ac 1
      _ ≤ (d : ℕ) := hcd_le
  have h3_le : (3 : ℕ) ≤ (d : ℕ) := by
    have h0 : (0 : ℕ) ≤ (a : ℕ) := Nat.zero_le _
    have h0_3 : 0 + 3 ≤ (a : ℕ) + 3 := Nat.add_le_add_right h0 3
    calc (3 : ℕ) = 0 + 3 := by simp
      _ ≤ (a : ℕ) + 3 := h0_3
      _ ≤ (d : ℕ) := h_ad
  have hd_lt : (d : ℕ) < n := d.is_lt
  have h3_lt : (3 : ℕ) < n := Nat.lt_of_le_of_lt h3_le hd_lt
  have h_contra : n < n := Nat.lt_of_le_of_lt hn h3_lt
  exact Nat.lt_irrefl n h_contra

end NoncrossingPartition
