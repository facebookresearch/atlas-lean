/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SetSplittingSetSizeAtMostThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.SetSplittingSetSizeAtMostThree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open SetSplitting (SetSplittingInstance SetSplittingFeasible)

private theorem accepts_encoding (i : SetSplittingInstance) :
    setSplittingSetSizeAtMostThreeDec (bitEncode i) = true ↔
      WellFormed i ∧ SetSplittingFeasible i := by
  simp [setSplittingSetSizeAtMostThreeDec, bitDecode_bitEncode]

/-- Feasibility ranges over the finitely many subsets of `{0, ..., n - 1}`. -/
private theorem feasible_iff_powerset (i : SetSplittingInstance) :
    SetSplittingFeasible i ↔ ∃ S ∈ (Finset.range i.1).powerset,
      ∀ s ∈ i.2, (∃ x ∈ s, x ∈ S) ∧ ∃ y ∈ s, y ∉ S := by
  simp [SetSplittingFeasible, Finset.subset_iff]

/-- A lone continuation bit is a truncated instance encoding. -/
example : setSplittingSetSizeAtMostThreeDec [true] = false := by
  have h : bitDecode (α := SetSplittingInstance) [true] = none := rfl
  simp [setSplittingSetSizeAtMostThreeDec, h]

/-- The part `{1}` splits both `{0, 1}` and `{1, 2}`. -/
example :
    setSplittingSetSizeAtMostThreeDec
      (bitEncode ((3, [[0, 1], [1, 2]]) : SetSplittingInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed SetSplitting.WellFormed; decide, {1}, by decide, by decide⟩

/-- Splitting the three edges of a triangle would two-color an odd cycle. -/
example :
    setSplittingSetSizeAtMostThreeDec
      (bitEncode ((3, [[0, 1], [1, 2], [0, 2]]) : SetSplittingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hf := ((accepts_encoding _).1 h).2
  rw [feasible_iff_powerset] at hf
  revert hf
  decide

/-- A four-element set is outside the size-three restriction, although `{0}` splits it. -/
example :
    setSplittingSetSizeAtMostThreeDec
      (bitEncode ((4, [[0, 1, 2, 3]]) : SetSplittingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2 [0, 1, 2, 3] (by simp)
  revert hw
  decide

end MetaMathlibExt.Complexity.NPComplete.SetSplittingSetSizeAtMostThree
