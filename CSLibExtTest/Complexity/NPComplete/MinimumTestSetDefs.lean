/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinimumTestSetDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSet

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MinimumTestSetInstance) :
    minimumTestSetDec (bitEncode i) = true ↔ WellFormed i ∧ MinimumTestSetFeasible i := by
  simp [minimumTestSetDec, bitDecode_bitEncode]

/-- Feasibility ranges over the finitely many sublists of `C`. -/
private theorem feasible_iff_sublists (i : MinimumTestSetInstance) :
    MinimumTestSetFeasible i ↔ ∃ T ∈ i.2.1.sublists, T.length ≤ i.2.2 ∧
      ∀ a < i.1, ∀ b < i.1, a ≠ b → ∃ s ∈ T, (a ∈ s ∧ b ∉ s) ∨ (a ∉ s ∧ b ∈ s) := by
  simp only [MinimumTestSetFeasible, List.mem_sublists]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minimumTestSetDec [true] = false := by
  have h : bitDecode (α := MinimumTestSetInstance) [true] = none := rfl
  simp [minimumTestSetDec, h]

set_option synthInstance.maxSize 1024 in
/-- The tests `{0}` and `{1}` distinguish every pair of elements of `{0, 1, 2}`. -/
example :
    minimumTestSetDec (bitEncode ((3, [[0], [1]], 2) : MinimumTestSetInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [[0], [1]], by decide, by decide, by decide⟩

set_option synthInstance.maxSize 4096 in
/-- A single test cannot distinguish all three pairs of `{0, 1, 2}`. -/
example :
    minimumTestSetDec (bitEncode ((3, [[0], [1]], 1) : MinimumTestSetInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hf := ((accepts_encoding _).1 h).2
  rw [feasible_iff_sublists] at hf
  revert hf
  decide

/-- A test listing an element twice is malformed. -/
example :
    minimumTestSetDec (bitEncode ((2, [[0, 0]], 1) : MinimumTestSetInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1
  revert hw
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSet
