/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.AssociationTests.CaseOnlyInteraction
import Mathlib.Tactic.NormNum

open WantedExt.Biology.StatisticalGenetics.CaseOnlyInteractionWanted

example (a b c d e f g h : ℝ) :
    riskRatioInteraction a b c d e f g h =
      (g / (g + h) / (a / (a + b))) /
        ((c / (c + d) / (a / (a + b))) * (e / (e + f) / (a / (a + b)))) := rfl

example (a b c d e f g h : ℝ) :
    oddsRatioInteraction a b c d e f g h =
      (b * g / (a * h)) / ((b * c / (a * d)) * (b * e / (a * f))) := rfl

example (a c e g : ℝ) : caseOnlyOddsRatio a c e g = a * g / (c * e) := rfl

example :
    ∃ a b c d e f g h : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧
      riskRatioInteraction a b c d e f g h = 1 ∧ oddsRatioInteraction a b c d e f g h = 1 ∧
      caseOnlyOddsRatio a c e g ≠ 1 := exists_caseOnly_ne_one

-- A positive normalized table with dependence both in the population and among the non-cases.
example :
    let a : ℝ := 1 / 6
    let b : ℝ := 1 / 6
    let c : ℝ := 1 / 12
    let d : ℝ := 1 / 12
    let e : ℝ := 1 / 12
    let f : ℝ := 1 / 12
    let g : ℝ := 1 / 6
    let h : ℝ := 1 / 6
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧
      a + b + c + d + e + f + g + h = 1 ∧
      (g + h) * (a + b) ≠ (c + d) * (e + f) ∧ b * h ≠ d * f ∧
      riskRatioInteraction a b c d e f g h = 1 ∧ oddsRatioInteraction a b c d e f g h = 1 ∧
      caseOnlyOddsRatio a c e g = 4 := by
  norm_num [riskRatioInteraction, oddsRatioInteraction, caseOnlyOddsRatio]

-- Independently compute both ratios from their formulas on a normalized table with non-case
-- independence but not population independence. The formula checks above connect them to the API.
example :
    let a : ℝ := 1 / 36
    let b : ℝ := 2 / 36
    let c : ℝ := 5 / 36
    let d : ℝ := 3 / 36
    let e : ℝ := 7 / 36
    let f : ℝ := 4 / 36
    let g : ℝ := 8 / 36
    let h : ℝ := 6 / 36
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧
      a + b + c + d + e + f + g + h = 1 ∧ b * h = d * f ∧
      (g + h) * (a + b) ≠ (c + d) * (e + f) ∧
      (b * g / (a * h)) / ((b * c / (a * d)) * (b * e / (a * f))) = 8 / 35 ∧
      a * g / (c * e) = 8 / 35 := by
  norm_num

-- The same table as counts tests the public theorem without a normalization step.
example : oddsRatioInteraction 1 2 5 3 7 4 8 6 = caseOnlyOddsRatio 1 5 7 8 := by
  apply oddsRatioInteraction_eq_caseOnly <;> norm_num
