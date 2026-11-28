/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.AssociationTests.RiskEffectCollapsibility
import Mathlib.Tactic.NormNum

open WantedExt.Biology.StatisticalGenetics.OddsRatioCollapsibilityWanted

private noncomputable def baseline (z : Bool) : ℝ :=
  if z then 1 / 4 else 1 / 3

private noncomputable def differenceRisks (x z : Bool) : ℝ :=
  if x then baseline z + 1 / 5 else baseline z

private noncomputable def ratioRisks (x z : Bool) : ℝ :=
  if x then 2 * baseline z else baseline z

example :
    ((2 / 3 : ℝ) * differenceRisks true true + (1 - 2 / 3) * differenceRisks true false) -
      ((2 / 3 : ℝ) * differenceRisks false true + (1 - 2 / 3) * differenceRisks false false) =
        1 / 5 := by
  apply (riskDifference_riskRatio_collapse (2 / 3) (by norm_num) (by norm_num)
    differenceRisks (1 / 5) 1).1
  intro z
  cases z <;> norm_num [differenceRisks, baseline]

example :
    (2 / 3 : ℝ) * ratioRisks true true + (1 - 2 / 3) * ratioRisks true false =
      2 * ((2 / 3 : ℝ) * ratioRisks false true + (1 - 2 / 3) * ratioRisks false false) := by
  apply (riskDifference_riskRatio_collapse (2 / 3) (by norm_num) (by norm_num)
    ratioRisks 0 2).2
  intro z
  rfl
