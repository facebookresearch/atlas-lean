/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SetPackingSetSizeAtMostThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.SetPackingSetSizeAtMostThree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open SetPacking (SetPackingInstance SetPackingFeasible)

private theorem accepts_encoding (i : SetPackingInstance) :
    setPackingSetSizeAtMostThreeDec (bitEncode i) = true ↔
      WellFormed i ∧ SetPackingFeasible i := by
  simp [setPackingSetSizeAtMostThreeDec, bitDecode_bitEncode]

/-- Feasibility ranges over the finitely many sublists of `C`. -/
private theorem feasible_iff_sublists (i : SetPackingInstance) :
    SetPackingFeasible i ↔ ∃ sub ∈ i.2.1.sublists, sub.Nodup ∧ i.2.2 ≤ sub.length ∧
      ∀ s1 ∈ sub, ∀ s2 ∈ sub, s1 ≠ s2 → ∀ x ∈ s1, x ∉ s2 := by
  simp only [SetPackingFeasible, List.mem_sublists]

/-- A lone continuation bit is a truncated instance encoding. -/
example : setPackingSetSizeAtMostThreeDec [true] = false := by
  have h : bitDecode (α := SetPackingInstance) [true] = none := rfl
  simp [setPackingSetSizeAtMostThreeDec, h]

/-- The triples `{0, 1, 2}` and `{3, 4, 5}` are disjoint. -/
example :
    setPackingSetSizeAtMostThreeDec
      (bitEncode ((6, [[0, 1, 2], [2, 3], [3, 4, 5]], 2) : SetPackingInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed SetPacking.WellFormed; decide, [[0, 1, 2], [3, 4, 5]], by decide,
    by decide, by decide, by decide⟩

set_option synthInstance.maxSize 4096 in
/-- The middle set `{2, 3}` meets both triples, so no three sets are pairwise disjoint. -/
example :
    setPackingSetSizeAtMostThreeDec
      (bitEncode ((6, [[0, 1, 2], [2, 3], [3, 4, 5]], 3) : SetPackingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hf := ((accepts_encoding _).1 h).2
  rw [feasible_iff_sublists] at hf
  revert hf
  decide

/-- A four-element set is outside the size-three restriction, although it packs alone. -/
example :
    setPackingSetSizeAtMostThreeDec
      (bitEncode ((4, [[0, 1, 2, 3]], 1) : SetPackingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2.1 [0, 1, 2, 3] (by simp)
  revert hw
  decide

end MetaMathlibExt.Complexity.NPComplete.SetPackingSetSizeAtMostThree
