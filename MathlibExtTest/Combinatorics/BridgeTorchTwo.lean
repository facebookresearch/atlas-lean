/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BridgeTorchTwo
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.BridgeTorchGeneralizations

-- Finishing requires an empty left bank and the torch on the right.
example : bridgeScheduleFrom 2 {1, 2} ∅ false [] = true ∧
    bridgeScheduleFrom 2 {1, 2} ∅ true [] = false := by decide

-- A pair can carry the torch back together, but a person still on the left cannot return.
example : IsBridgeSchedule 2 2 [{1, 2}, {1, 2}, {1, 2}] ∧
    ¬ IsBridgeSchedule 2 2 [{1}, {2}, {1, 2}] := by
  unfold IsBridgeSchedule
  decide

-- Both the smallest admissible population and an odd population have the stated optimum.
example : bridgeTime 2 2 = 2 := by
  have h := bridgeTime_two_closed_form 2 (by decide)
  norm_num at h
  exact_mod_cast h

example : IsBridgeSchedule 2 5 [{1, 2}, {2}, {4, 5}, {1}, {1, 2}, {1}, {1, 3}] ∧
    scheduleCost [{1, 2}, {2}, {4, 5}, {1}, {1, 2}, {1}, {1, 3}] = bridgeTime 2 5 := by
  refine ⟨by unfold IsBridgeSchedule; decide, ?_⟩
  have h := bridgeTime_two_closed_form 5 (by decide)
  norm_num at h
  change 16 = bridgeTime 2 5
  exact_mod_cast h.symm

end MetaMathlibExt.BridgeTorchGeneralizations
