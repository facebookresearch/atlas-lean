/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ComparativeContainmentUnitWeightsDefs

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeContainmentUnitWeights

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open ComparativeContainment (containingWeight WeightedSubsetWellFormed)

/-- `X = {0, 1}`; the empty `Y` loses `3` to `2`, while `Y = {0}` lies in no member of `S`. -/
private abbrev yes : ComparativeContainmentUnitWeightsInstance :=
  (2, [([0], 1), ([0, 1], 1)], [([], 1), ([1], 1), ([1], 1)])

/-- `X = {0}`; the empty `Y` loses `3` to `1` and `Y = {0}` loses `2` to `1`. -/
private abbrev no : ComparativeContainmentUnitWeightsInstance :=
  (1, [([0], 1)], [([], 1), ([0], 1), ([0], 1)])

/-- A weighted instance that is feasible with `Y = ∅` but has a weight of `2`. -/
private abbrev heavy : ComparativeContainmentUnitWeightsInstance := (0, [([], 2)], [([], 1)])

/-- The decision problem accepts `yes`, with witness `Y = {0}`. -/
example : comparativeContainmentUnitWeightsDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by
    unfold WellFormed ComparativeContainment.WellFormed WeightedSubsetWellFormed; decide
  have hf : ComparativeContainmentUnitWeightsFeasible yes := ⟨{0}, by decide⟩
  simp [comparativeContainmentUnitWeightsDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed instance `no`: every `Y ⊆ X` loses. -/
example : WellFormed no ∧ comparativeContainmentUnitWeightsDec (bitEncode no) = false := by
  have hf : ¬ ComparativeContainmentUnitWeightsFeasible no := by
    unfold ComparativeContainmentUnitWeightsFeasible
      ComparativeContainment.ComparativeContainmentFeasible
    decide
  exact ⟨by unfold WellFormed ComparativeContainment.WellFormed WeightedSubsetWellFormed; decide,
    by simp [comparativeContainmentUnitWeightsDec, bitDecode_bitEncode, hf]⟩

/-- The unit-weight condition is what rejects `heavy`: it is a well-formed, feasible weighted
instance, yet this decision problem rejects it. -/
example :
    ComparativeContainment.WellFormed heavy ∧ ComparativeContainmentUnitWeightsFeasible heavy ∧
      comparativeContainmentUnitWeightsDec (bitEncode heavy) = false := by
  have hw : ¬ WellFormed heavy := by
    unfold WellFormed ComparativeContainment.WellFormed WeightedSubsetWellFormed; decide
  exact ⟨by unfold ComparativeContainment.WellFormed WeightedSubsetWellFormed; decide,
    ⟨∅, by decide⟩, by simp [comparativeContainmentUnitWeightsDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : comparativeContainmentUnitWeightsDec [true] = false := by
  have h : bitDecode (α := ComparativeContainmentUnitWeightsInstance) [true] = none := rfl
  simp [comparativeContainmentUnitWeightsDec, h]

end MetaMathlibExt.Complexity.NPComplete.ComparativeContainmentUnitWeights
