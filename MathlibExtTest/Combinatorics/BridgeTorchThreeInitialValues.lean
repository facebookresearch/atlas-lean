/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BridgeTorchThreeInitialValues

namespace MetaMathlibExt.BridgeTorchGeneralizations

-- The fourth person is the first who cannot join a single crossing.
example : bridgeTime 3 4 = bridgeTime 3 3 + 4 := by
  obtain ⟨_, _, h₃, h₄, _, _⟩ := bridgeTime_three_initial_values
  rw [h₃, h₄]

-- A different optimal schedule for six people returns the torch twice with person 1.
example :
    let σ : List (Finset ℕ) := [{1, 2}, {1}, {1, 3, 4}, {1}, {1, 5, 6}]
    IsBridgeSchedule 3 6 σ ∧ scheduleCost σ = bridgeTime 3 6 := by
  obtain ⟨_, _, _, _, _, h₆⟩ := bridgeTime_three_initial_values
  rw [h₆]
  unfold IsBridgeSchedule
  decide

end MetaMathlibExt.BridgeTorchGeneralizations
