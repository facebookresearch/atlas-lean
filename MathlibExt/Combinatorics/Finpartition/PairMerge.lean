/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic

/-!
# The uniform pair-merger walk on finite set partitions

The walk coarsens a partition by choosing an unordered pair of distinct blocks uniformly and
merging them. The empty partition and the one-block partition are absorbing.
-/

@[expose] public section

namespace Finpartition

open Finset

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- `Q` is obtained from `P` by merging two blocks: it coarsens `P` and has one fewer block. -/
def IsPairMerge (P Q : Finpartition s) : Prop :=
  P ≤ Q ∧ #Q.parts + 1 = #P.parts

open scoped Classical in
/-- One step of the uniform pair-merger walk on the partitions of `s`. -/
noncomputable def pairMergeMatrix (s : Finset α) : Matrix (Finpartition s) (Finpartition s) ℝ :=
  Matrix.of fun P Q =>
    if 2 ≤ #P.parts then (if IsPairMerge P Q then (((#P.parts).choose 2 : ℕ) : ℝ)⁻¹ else 0)
    else if P = Q then 1 else 0

/-- The probability of a specified merger from a partition with at least two blocks. -/
theorem pairMergeMatrix_of_merge {P Q : Finpartition s} (hP : 2 ≤ #P.parts) (h : IsPairMerge P Q) :
    pairMergeMatrix s P Q = (((#P.parts).choose 2 : ℕ) : ℝ)⁻¹ := by
  classical
  simp [pairMergeMatrix, hP, h]

/-- When there is no pair of blocks to merge, the partition stays fixed. -/
@[simp] theorem pairMergeMatrix_self_of_lt_two (P : Finpartition s) (h : #P.parts < 2) :
    pairMergeMatrix s P P = 1 := by
  classical
  simp [pairMergeMatrix, h.not_ge]

end Finpartition
