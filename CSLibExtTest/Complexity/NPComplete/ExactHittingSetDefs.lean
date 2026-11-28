/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ExactHittingSetDefs

namespace MetaMathlibExt.Complexity.NPComplete.ExactHittingSet

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- A hitting set may be taken among the subsets of `{0, …, r - 1}`. -/
private theorem feasible_iff (i : ExactHittingSetInstance) :
    ExactHittingSetFeasible i ↔
      ∃ W ∈ (Finset.range i.1).powerset, ∀ s ∈ i.2, (s.filter (· ∈ W)).length = 1 := by
  simp only [ExactHittingSetFeasible, Finset.mem_powerset, Finset.subset_iff, Finset.mem_range]

/-- Subsets of `{0, 1, 2, 3}` that `{0, 3}` meets exactly once each. -/
private abbrev yes : ExactHittingSetInstance := (4, [[0, 1], [1, 3], [2, 3], [0, 2]])

/-- `[0]` forces `0` and `[1]` forces `1`, so `[0, 1]` is met twice. -/
private abbrev no : ExactHittingSetInstance := (2, [[0], [1], [0, 1]])

/-- The decision problem accepts `yes`, with witness `{0, 3}`. -/
example : exactHittingSetDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed; decide
  have hf : ExactHittingSetFeasible yes := ⟨{0, 3}, by decide, by decide⟩
  simp [exactHittingSetDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed instance `no`. -/
example : WellFormed no ∧ exactHittingSetDec (bitEncode no) = false := by
  have hf : ¬ ExactHittingSetFeasible no := by rw [feasible_iff]; decide
  exact ⟨by unfold WellFormed; decide, by simp [exactHittingSetDec, bitDecode_bitEncode, hf]⟩

/-- A subset with a repeated entry is malformed: `{1}` meets `[0, 0, 1]` exactly once, yet the
decision problem rejects the instance. -/
example :
    ExactHittingSetFeasible ((2, [[0, 0, 1]]) : ExactHittingSetInstance) ∧
      exactHittingSetDec (bitEncode ((2, [[0, 0, 1]]) : ExactHittingSetInstance)) = false := by
  have hw : ¬ WellFormed ((2, [[0, 0, 1]]) : ExactHittingSetInstance) := by
    unfold WellFormed; decide
  exact ⟨⟨{1}, by decide, by decide⟩, by simp [exactHittingSetDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : exactHittingSetDec [true] = false := by
  have h : bitDecode (α := ExactHittingSetInstance) [true] = none := rfl
  simp [exactHittingSetDec, h]

end MetaMathlibExt.Complexity.NPComplete.ExactHittingSet
