/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ComparativeContainmentDefs

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeContainment

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- `X = {0, 1}`; the empty `Y` loses `5` to `2`, while `Y = {0}` wins `2` to `1`. -/
private abbrev yes : ComparativeContainmentInstance :=
  (2, [([0, 1], 2)], [([0], 1), ([1], 1), ([], 3)])

/-- `X = {0}`; the empty `Y` loses `3` to `1` and `Y = {0}` loses `2` to `1`. -/
private abbrev no : ComparativeContainmentInstance := (1, [([0], 1)], [([], 1), ([0], 2)])

/-- The decision problem accepts `yes`, with witness `Y = {0}`. -/
example : comparativeContainmentDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed WeightedSubsetWellFormed; decide
  have hf : ComparativeContainmentFeasible yes := ⟨{0}, by decide⟩
  simp [comparativeContainmentDec, bitDecode_bitEncode, hw, hf]

/-- The empty `Y` alone does not witness `yes`. -/
example : ¬ containingWeight (n := 2) yes.2.2 ∅ ≤ containingWeight (n := 2) yes.2.1 ∅ := by
  decide

/-- The decision problem rejects the well-formed instance `no`: every `Y ⊆ X` loses. -/
example : WellFormed no ∧ comparativeContainmentDec (bitEncode no) = false := by
  have hf : ¬ ComparativeContainmentFeasible no := by unfold ComparativeContainmentFeasible; decide
  exact ⟨by unfold WellFormed WeightedSubsetWellFormed; decide,
    by simp [comparativeContainmentDec, bitDecode_bitEncode, hf]⟩

/-- A zero weight is malformed, although the instance is feasible with `Y = ∅`. -/
example :
    ComparativeContainmentFeasible ((0, [([], 0)], []) : ComparativeContainmentInstance) ∧
      comparativeContainmentDec
        (bitEncode ((0, [([], 0)], []) : ComparativeContainmentInstance)) = false := by
  have hw : ¬ WellFormed ((0, [([], 0)], []) : ComparativeContainmentInstance) := by
    unfold WellFormed WeightedSubsetWellFormed; decide
  exact ⟨⟨∅, by decide⟩, by simp [comparativeContainmentDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : comparativeContainmentDec [true] = false := by
  have h : bitDecode (α := ComparativeContainmentInstance) [true] = none := rfl
  simp [comparativeContainmentDec, h]

end MetaMathlibExt.Complexity.NPComplete.ComparativeContainment
