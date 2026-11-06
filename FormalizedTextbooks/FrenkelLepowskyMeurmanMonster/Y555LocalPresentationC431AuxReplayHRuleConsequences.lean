/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original-group equations for all H auxiliary symbols of the C431 trace. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayHRuleChecks

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Interpret an H operation using only literal original-source word values. -/
def y431AuxReplayHRuleValue : Y431AuxReplayHRule → Y431RPresentation
  | .one => 1
  | .generator v => PresentedGroup.of v
  | .mul a b _ => y431PositiveWord (y431AuxReplayHWord a) *
      y431PositiveWord (y431AuxReplayHWord b)
  | .inv a _ => (y431PositiveWord (y431AuxReplayHWord a))⁻¹
  | .reverse a => (y431PositiveWord (y431AuxReplayHWord a))⁻¹

set_option maxRecDepth 100000 in
/-- Every actual H definition holds by the checked original-source Coxeter normalizations. -/
theorem y431AuxReplayHRule_valid (i : Fin 620) :
    y431PositiveWord (y431AuxReplayHWord i) =
      y431AuxReplayHRuleValue (y431AuxReplayHRule i) := by
  have hc := y431AuxReplayHRule_checked i
  cases hr : y431AuxReplayHRule i with
  | one =>
    simp only [y431AuxReplayHRuleChecked, hr] at hc
    change y431PositiveWord (y431AuxReplayHWord i) = 1
    simp only [hc, y431PositiveWord, List.map_nil, List.prod_nil]
  | generator v =>
    simp only [y431AuxReplayHRuleChecked, hr] at hc
    change y431PositiveWord (y431AuxReplayHWord i) = PresentedGroup.of v
    simp only [hc, y431PositiveWord, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  | mul a b c =>
    simp only [y431AuxReplayHRuleChecked, hr] at hc
    have hn := y431AuxE8Certificate_valid c
    rw [hc.1, hc.2, y431PositiveWord_append] at hn
    exact hn.symm
  | inv a c =>
    simp only [y431AuxReplayHRuleChecked, hr] at hc
    have hn := y431AuxE8Certificate_valid c
    rw [hc.1, hc.2, y431PositiveWord_reverse] at hn
    exact hn.symm
  | reverse a =>
    simp only [y431AuxReplayHRuleChecked, hr] at hc
    change y431PositiveWord (y431AuxReplayHWord i) =
      (y431PositiveWord (y431AuxReplayHWord a))⁻¹
    simp only [hc, y431PositiveWord_reverse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
