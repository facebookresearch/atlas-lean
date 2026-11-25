/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BridgeTorchStar
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.BridgeTorchGeneralizations

-- Four people can leave simultaneously along two edges when each pair has a torch.
private def twoPairs : List (StarMove 4 2) :=
  [⟨{0, 1}, 0, true⟩, ⟨{2, 3}, 1, true⟩]

example : IsStarSchedule 4 2 2 [twoPairs] ∧ starStepDuration twoPairs = 4 := by
  unfold IsStarSchedule
  decide

example : ¬ IsStarSchedule 4 2 1 [twoPairs] := by
  unfold IsStarSchedule
  decide

-- With five people and two edges, the last batch consists of the fastest person alone.
example : starTime 5 2 3 = 6 := by
  have h := (starTime_bounds 5 2 3 (by decide) (by decide) (by decide)).2.2.1 (by decide)
  norm_num at h
  exact_mod_cast h

-- One torch limits a three-edge star to a single movement per step.
example : 4 ≤ starTime 3 3 1 ∧ starTime 3 3 1 ≤ bridgeTime 2 3 := by
  have h := starTime_bounds 3 3 1 (by decide) (by decide) (by decide)
  have hlo := h.1
  norm_num at hlo
  exact ⟨by exact_mod_cast hlo, h.2.1⟩

end MetaMathlibExt.BridgeTorchGeneralizations
