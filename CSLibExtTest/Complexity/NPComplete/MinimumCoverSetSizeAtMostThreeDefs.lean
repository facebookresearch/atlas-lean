/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinimumCoverSetSizeAtMostThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCoverSetSizeAtMostThree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open SetCover (SetCoverInstance SetCoverFeasible)

private theorem accepts_encoding (i : SetCoverInstance) :
    minimumCoverSetSizeAtMostThreeDec (bitEncode i) = true ↔
      WellFormed i ∧ SetCoverFeasible i := by
  simp [minimumCoverSetSizeAtMostThreeDec, bitDecode_bitEncode]

/-- Feasibility ranges over the finitely many sublists of `C`. -/
private theorem feasible_iff_sublists (i : SetCoverInstance) :
    SetCoverFeasible i ↔ ∃ sub ∈ i.2.1.sublists, sub.length ≤ i.2.2 ∧
      ∀ x < i.1, ∃ s ∈ sub, x ∈ s := by
  simp [SetCoverFeasible, List.mem_sublists]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minimumCoverSetSizeAtMostThreeDec [true] = false := by
  have h : bitDecode (α := SetCoverInstance) [true] = none := rfl
  simp [minimumCoverSetSizeAtMostThreeDec, h]

/-- The sets `{0, 1}` and `{2}` cover `{0, 1, 2}` within the bound two. -/
example :
    minimumCoverSetSizeAtMostThreeDec
      (bitEncode ((3, [[0, 1], [2], [1, 2]], 2) : SetCoverInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed SetCover.WellFormed; decide, [[0, 1], [2]], by decide,
    by decide, by decide⟩

/-- No single set covers `{0, 1, 2}`. -/
example :
    minimumCoverSetSizeAtMostThreeDec
      (bitEncode ((3, [[0, 1], [2], [1, 2]], 1) : SetCoverInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hf := ((accepts_encoding _).1 h).2
  rw [feasible_iff_sublists] at hf
  revert hf
  decide

/-- A four-element set is outside the size-three restriction, although it covers `S` alone. -/
example :
    minimumCoverSetSizeAtMostThreeDec
      (bitEncode ((4, [[0, 1, 2, 3]], 1) : SetCoverInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2.1 [0, 1, 2, 3] (by simp)
  revert hw
  decide

end MetaMathlibExt.Complexity.NPComplete.MinimumCoverSetSizeAtMostThree
