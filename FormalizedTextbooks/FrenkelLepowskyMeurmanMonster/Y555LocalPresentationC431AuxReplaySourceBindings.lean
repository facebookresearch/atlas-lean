/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact original-source binding of every declared C431 contextual replay source. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplaySourceFamilies
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayProgram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A declared source must match an independently proved original-group equation exactly. -/
def y431AuxReplaySourceBound (i : Fin 856) : Prop :=
  y322EquationsSameReduction (y431AuxReplaySourceEquation i) (y431AuxReplaySourceFamily i)

/-- Literal source-side binding is decidable in the exact finite replay alphabet. -/
instance y431AuxReplaySourceBoundDecidable (i : Fin 856) :
    Decidable (y431AuxReplaySourceBound i) := by
  unfold y431AuxReplaySourceBound y322EquationsSameReduction
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- This finite check binds every literal trace source to its independently proved source family.
/-- All eight hundred fifty-six declared sources retain their exact proved original-source sides. -/
theorem y431AuxReplaySource_bound (i : Fin 856) : y431AuxReplaySourceBound i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
