/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.AssociationTests.RiskEffectCollapsibility
import Mathlib.Data.Fintype.BigOperators
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

-- Use the stratum risks of Table 1 with independent, unequal marginal weights:
-- P(X = 1) = 2/5 and P(Z = 1) = 2/3.
private noncomputable def asymmetricMass : Bool → Bool → Bool → ℝ
  | true, true, true => 16 / 75
  | true, true, false => 4 / 75
  | true, false, true => 4 / 75
  | true, false, false => 6 / 75
  | false, true, true => 18 / 75
  | false, true, false => 3 / 75
  | false, false, true => 12 / 75
  | false, false, false => 12 / 75

-- Compute both sides independently for both treatment values.
example (x : Bool) :
    crudeRisk asymmetricMass x = (if x then 2 / 3 else 7 / 15) ∧
      (∑ z, massZ asymmetricMass z * stratumRisk asymmetricMass x z) =
        (if x then 2 / 3 else 7 / 15) := by
  cases x <;> norm_num [crudeRisk.eq_def, stratumRisk.eq_def, massX.eq_def, massZ.eq_def,
    massXZ.eq_def, Fintype.sum_bool, asymmetricMass]

-- The standardized and crude ratios both equal 10/7, even though the strata have different ratios.
example :
    (∑ z, massZ asymmetricMass z * stratumRisk asymmetricMass true z) /
        (∑ z, massZ asymmetricMass z * stratumRisk asymmetricMass false z) = 10 / 7 ∧
      crudeRisk asymmetricMass true / crudeRisk asymmetricMass false = 10 / 7 := by
  norm_num [crudeRisk.eq_def, stratumRisk.eq_def, massX.eq_def, massZ.eq_def, massXZ.eq_def,
    Fintype.sum_bool, asymmetricMass]

-- Client example: the concrete table satisfies every hypothesis of the public theorem.
example :
    (∀ x, crudeRisk asymmetricMass x = ∑ z, massZ asymmetricMass z * stratumRisk asymmetricMass x z) ∧
      (∑ z, massZ asymmetricMass z * stratumRisk asymmetricMass true z) /
        (∑ z, massZ asymmetricMass z * stratumRisk asymmetricMass false z) =
          crudeRisk asymmetricMass true / crudeRisk asymmetricMass false := by
  apply crudeRisk_eq_mixture
  · intro x y z
    cases x <;> cases y <;> cases z <;> norm_num [asymmetricMass]
  · norm_num [Fintype.sum_bool, asymmetricMass]
  · intro x z
    cases x <;> cases z <;> norm_num [massXZ.eq_def, massX.eq_def, massZ.eq_def,
      Fintype.sum_bool, asymmetricMass]
  · intro x z
    cases x <;> cases z <;> norm_num [massXZ.eq_def, Fintype.sum_bool, asymmetricMass]
  · norm_num [crudeRisk.eq_def, massX.eq_def, Fintype.sum_bool, asymmetricMass]
