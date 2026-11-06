/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact original C431/R cubic identity from independently checked original-source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayTargets

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- The original defining-relation loop forces its concrete E8 coefficient to be the identity. -/
theorem y431AuxReplay_loop_coefficient_one : y431PositiveWord (y431AuxReplayHWord 619) = 1 := by
  have h := y431AuxReplayProgram_valid 3683
  change y431AuxReplayWordValue (y431AuxReplayProgram 3683).1.left =
    y431AuxReplayWordValue (y431AuxReplayProgram 3683).1.right at h
  rw [y431AuxReplayLoop_equation.1, y431AuxReplayLoop_equation.2,
    y431AuxReplayWordValue_singleton, y431AuxReplayHSymbol_value,
    y431AuxReplayWordValue_nil] at h
  exact h

set_option maxRecDepth 100000 in
/-- The exact original C431/R longest-word/e1 cube equals one by its original source relations. -/
theorem y431LongestCube_eq_one : PresentedGroup.mk y431Relations y431LongestCube = 1 := by
  have h := y431AuxReplayProgram_valid 3660
  change y431AuxReplayWordValue (y431AuxReplayProgram 3660).1.left =
    y431AuxReplayWordValue (y431AuxReplayProgram 3660).1.right at h
  rw [y431AuxReplayCube_equation.1, y431AuxReplayCube_equation.2,
    y431AuxReplayCubeSignedWord_value, y431AuxReplayWordValue_singleton,
    y431AuxReplayHSymbol_value, y431AuxReplayHWord_target_eq_loop] at h
  exact h.trans y431AuxReplay_loop_coefficient_one

/-- The original F12/e1 word satisfies its cubic relation in the original quotient. -/
theorem y431F12_e1_cube :
    (PresentedGroup.mk y431Relations y431F12 * (PresentedGroup.of 4 : Y431RPresentation)) ^ 3 =
      1 := by
  simpa only [y431LongestCube, map_pow, map_mul, PresentedGroup.of] using y431LongestCube_eq_one

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
