/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

@[expose] public section

/-!
# Overpartitions

An overpartition of `n` is a partition of `n` in which the first (equivalently, last)
occurrence of each distinct part may be overlined. Since `Nat.Partition` stores an
unordered multiset, the overlining data are represented by a choice of distinct part
sizes occurring in the underlying partition. The two conventions are equivalent: each
records one binary choice per distinct occurring part size, and the unordered multiset
carries no order to distinguish first from last.

## Main definitions

* `Nat.Overpartition` is an overpartition with a specified underlying partition and overlined sizes.
* `Nat.Overpartition.IsOverlined` says that a part size is overlined.
* `Nat.Overpartition.ofPartition` equips a partition with no overlined sizes.
* `Nat.Overpartition.full` equips a partition with every distinct part size overlined.

## References

* [B. Hemanthkumar and H. S. Sumanth Bharadwaj, *Arithmetic properties of
  2^α-Regular overpartition pairs*](https://arxiv.org/abs/2502.17312)
* [J. Aniceto and C. Ballantine, *Identities involving the number of missing integers in
  partitions - combinatorial proofs*](https://arxiv.org/abs/2608.00278)
* [G. Andrews and M. Ghosh Dastidar, *The Partition Pairing
  Theorems I*](https://arxiv.org/abs/2608.22291)
-/

namespace Nat

/-- An overpartition of `n`, represented by an underlying partition and its overlined part sizes. -/
@[ext]
structure Overpartition (n : ℕ) where
  /-- The underlying partition. -/
  toPartition : Partition n
  /-- The distinct part sizes that are overlined. -/
  overlines : Finset ℕ
  /-- Every overlined size occurs in the underlying partition. -/
  overlines_subset : overlines ⊆ toPartition.parts.toFinset
deriving DecidableEq

namespace Overpartition

/-- `a` is overlined in the overpartition `O`. -/
def IsOverlined {n : ℕ} (O : Overpartition n) (a : ℕ) : Prop :=
  a ∈ O.overlines

/-- Membership characterization for `IsOverlined`. -/
theorem isOverlined_iff {n : ℕ} {O : Overpartition n} {a : ℕ} :
    O.IsOverlined a ↔ a ∈ O.overlines :=
  Iff.rfl

/-- An overlined size occurs in the underlying multiset of parts. -/
theorem isOverlined_mem_parts {n : ℕ} {O : Overpartition n} {a : ℕ}
    (h : O.IsOverlined a) : a ∈ O.toPartition.parts :=
  Multiset.mem_toFinset.mp (O.overlines_subset h)

/-- An overlined size is positive. -/
theorem isOverlined_pos {n : ℕ} {O : Overpartition n} {a : ℕ}
    (h : O.IsOverlined a) : 0 < a :=
  O.toPartition.parts_pos (isOverlined_mem_parts h)

/-- Equip a partition with no overlined part sizes. -/
def ofPartition {n : ℕ} (p : Partition n) : Overpartition n where
  toPartition := p
  overlines := ∅
  overlines_subset := by simp

/-- The underlying partition of `ofPartition p` is `p`. -/
@[simp]
theorem ofPartition_toPartition {n : ℕ} (p : Partition n) :
    (ofPartition p).toPartition = p :=
  rfl

/-- The overlined sizes of `ofPartition p` are empty. -/
@[simp]
theorem ofPartition_overlines {n : ℕ} (p : Partition n) :
    (ofPartition p).overlines = ∅ :=
  rfl

/-- No size is overlined in `ofPartition p`. -/
@[simp]
theorem not_isOverlined_ofPartition {n : ℕ} (p : Partition n) (a : ℕ) :
    ¬ (ofPartition p).IsOverlined a := by
  simp [IsOverlined]

/-- Equip a partition with every distinct occurring part size overlined. -/
def full {n : ℕ} (p : Partition n) : Overpartition n where
  toPartition := p
  overlines := p.parts.toFinset
  overlines_subset := fun _ hx => hx

/-- The underlying partition of `full p` is `p`. -/
@[simp]
theorem full_toPartition {n : ℕ} (p : Partition n) :
    (full p).toPartition = p :=
  rfl

/-- The overlined sizes of `full p` are the distinct parts of `p`. -/
@[simp]
theorem full_overlines {n : ℕ} (p : Partition n) :
    (full p).overlines = p.parts.toFinset :=
  rfl

/-- A size is overlined in `full p` exactly when it occurs in `p`. -/
@[simp]
theorem isOverlined_full {n : ℕ} (p : Partition n) (a : ℕ) :
    (full p).IsOverlined a ↔ a ∈ p.parts := by
  simp [IsOverlined]

/-- An overpartition of zero has no overlined sizes. -/
theorem overlines_eq_empty_of_zero {O : Overpartition 0} : O.overlines = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have h := O.overlines_subset ha
  rw [Partition.partition_zero_parts] at h
  simp at h

/-- There is only one overpartition of zero. -/
theorem eq_of_zero (O₁ O₂ : Overpartition 0) : O₁ = O₂ := by
  apply Overpartition.ext
  · exact Subsingleton.elim _ _
  · rw [overlines_eq_empty_of_zero (O := O₁), overlines_eq_empty_of_zero (O := O₂)]

/-- `Overpartition n` is finite: it is equivalent to the dependent pairs of a partition of `n`
and a subset of its distinct part sizes. -/
instance instFintype (n : ℕ) : Fintype (Overpartition n) :=
  Fintype.ofEquiv (Σ p : Partition n, p.parts.toFinset.powerset)
    { toFun := fun x => ⟨x.1, x.2.1, Finset.mem_powerset.mp x.2.2⟩
      invFun := fun O =>
        ⟨O.toPartition, ⟨O.overlines, Finset.mem_powerset.mpr O.overlines_subset⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Overpartition
end Nat
