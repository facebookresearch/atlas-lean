/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SetPackingDefs

namespace MetaMathlibExt.Complexity.NPComplete.SetPacking

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SetPackingInstance) :
    setPackingDec (bitEncode i) = true ↔ WellFormed i ∧ SetPackingFeasible i := by
  simp [setPackingDec, bitDecode_bitEncode]

/-- Feasibility ranges over the finitely many sublists of `C`. -/
private theorem feasible_iff_sublists (i : SetPackingInstance) :
    SetPackingFeasible i ↔ ∃ sub ∈ i.2.1.sublists, sub.Nodup ∧ i.2.2 ≤ sub.length ∧
      ∀ s1 ∈ sub, ∀ s2 ∈ sub, s1 ≠ s2 → ∀ x ∈ s1, x ∉ s2 := by
  simp only [SetPackingFeasible, List.mem_sublists]

/-- A lone continuation bit is a truncated instance encoding. -/
example : setPackingDec [true] = false := by
  have h : bitDecode (α := SetPackingInstance) [true] = none := rfl
  simp [setPackingDec, h]

/-- The sets `{0, 1}` and `{2, 3}` are disjoint. -/
example :
    setPackingDec (bitEncode ((4, [[0, 1], [1, 2], [2, 3]], 2) : SetPackingInstance)) =
      true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [[0, 1], [2, 3]], by decide, by decide, by decide,
    by decide⟩

set_option synthInstance.maxSize 4096 in
/-- The middle set `{1, 2}` meets both others, so no three sets are pairwise disjoint. -/
example :
    setPackingDec (bitEncode ((4, [[0, 1], [1, 2], [2, 3]], 3) : SetPackingInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  have hf := ((accepts_encoding _).1 h).2
  rw [feasible_iff_sublists] at hf
  revert hf
  decide

/-- An element outside the universe is malformed. -/
example :
    setPackingDec (bitEncode ((2, [[0, 2]], 1) : SetPackingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1
  revert hw
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.SetPacking
