/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ScottishBook43
import Mathlib.Topology.Instances.Irrational

open Set MathlibExt.Topology.ScottishBook43Wanted

-- Both players may return the interval they were given, including forever.
example : BanachMazurStrategyValid id := fun _ h => ⟨h, Subset.rfl⟩

example (I : ℝ × ℝ) : BanachMazurPlayConsistent I id id (fun _ => I) :=
  ⟨rfl, fun _ => ⟨fun _ => rfl, fun _ => rfl⟩⟩

-- Local comeagreness suffices for the first player.
example : BanachMazurAHasWinningStrategy (Ioo (0 : ℝ) 1) := by
  apply (banach_mazur_winning_strategy_characterization _).1.2
  exact ⟨0, 1, zero_lt_one, by simpa using (IsMeagre.empty : IsMeagre (∅ : Set ℝ))⟩

-- The second player can avoid even the dense target consisting of all rational numbers.
example : BanachMazurBHasWinningStrategy (range ((↑) : ℚ → ℝ)) :=
  (banach_mazur_winning_strategy_characterization _).2.2 eventually_residual_irrational
