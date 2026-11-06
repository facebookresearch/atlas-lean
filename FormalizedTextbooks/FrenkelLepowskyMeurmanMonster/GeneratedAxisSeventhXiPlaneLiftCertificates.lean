/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneLiftData

/-! Ordinary kernel checks for every original source permutation step and central phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- These finite certificates check the original Q action, including every central phase.
/-- The initial twenty-four literal states are exactly the original binary-basis lifts. -/
theorem generatedSeventhXiPlaneQState_start : ∀ j : Fin 24,
    toAdd (generatedSeventhXiPlaneQState 0 j).base = toAdd (xiSpinBinaryBasisLift j).base ∧
      toAdd (generatedSeventhXiPlaneQState 0 j).coeff = toAdd (xiSpinBinaryBasisLift j).coeff := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- These finite certificates check the original Q action, including every central phase.
/-- Every actual forward or inverse source step retains its full central phase.
Inverse steps are certified by applying the genuine forward automorphism to the output. -/
theorem generatedSeventhXiPlaneQState_step : ∀ r : Fin 13, ∀ j : Fin 24,
    if h : (generatedSeventhXiPlaneLetters r).val < 2 then
      let q := monsterSourcePermutationImage ⟨(generatedSeventhXiPlaneLetters r).val, h⟩
        (generatedSeventhXiPlaneQState r.castSucc j)
      toAdd q.base = toAdd (generatedSeventhXiPlaneQState r.succ j).base ∧
        toAdd q.coeff = toAdd (generatedSeventhXiPlaneQState r.succ j).coeff
    else
      let q := monsterSourcePermutationImage
        ⟨(generatedSeventhXiPlaneLetters r).val - 2, by
          have _ht := (generatedSeventhXiPlaneLetters r).isLt
          omega⟩ (generatedSeventhXiPlaneQState r.succ j)
      toAdd q.base = toAdd (generatedSeventhXiPlaneQState r.castSucc j).base ∧
        toAdd q.coeff = toAdd (generatedSeventhXiPlaneQState r.castSucc j).coeff := by
  intro r
  fin_cases r <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
