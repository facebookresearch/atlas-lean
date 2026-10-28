/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original-group validity of every literal C431 auxiliary path definition. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayTChecks

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Interpret a declared T operation at its literal actual-group word values. -/
def y431AuxReplayTDefinitionValue : Y431AuxReplayTDefinition → Y431RPresentation
  | .one => 1
  | .append a g => y431AuxPositiveWord (y431AuxReplayTWord a) * y431AuxGenerator g

set_option maxRecDepth 100000 in
/-- Every T equation follows from the actual concatenation of its declared literal path words. -/
theorem y431AuxReplayTDefinition_valid (i : Fin 180) :
    y431AuxPositiveWord (y431AuxReplayTWord i) =
      y431AuxReplayTDefinitionValue (y431AuxReplayTDefinition i) := by
  have hc := y431AuxReplayTDefinition_checked i
  cases hd : y431AuxReplayTDefinition i with
  | one =>
    simp only [y431AuxReplayTDefinitionChecked, hd] at hc
    change y431AuxPositiveWord (y431AuxReplayTWord i) = 1
    simp only [hc, y431AuxPositiveWord, List.map_nil, List.prod_nil]
  | append a g =>
    simp only [y431AuxReplayTDefinitionChecked, hd] at hc
    change y431AuxPositiveWord (y431AuxReplayTWord i) =
      y431AuxPositiveWord (y431AuxReplayTWord a) * y431AuxGenerator g
    rw [hc, y431AuxPositiveWord_append]
    simp only [y431AuxPositiveWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
