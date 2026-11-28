/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasWeightedPowerSumAlphaBounds
import Mathlib.Tactic.NormNum

/-! # Tests for bounds on Lucas terms in terms of the dominant root -/

namespace MetaMathlibExt

private def negativeParams : LucasSequenceParams := ⟨3, -4, by decide⟩
private def positiveParams : LucasSequenceParams := ⟨5, 4, by decide⟩

-- At n = 2 the unconditional lower bound is attained.
example :
    let α : ℝ := (negativeParams.p + Real.sqrt (negativeParams.p ^ 2 - 4 * negativeParams.q)) / 2
    (negativeParams.p : ℝ) * α ^ (2 - 2 : ℕ) = lucasU negativeParams 2 := by
  have hU : lucasU negativeParams 2 = 3 := by decide
  dsimp only
  rw [hU]
  norm_num [negativeParams]

-- The roots are 4 and -1. At the odd index n = 3, the smaller root subtracts from V₃.
example :
    let α : ℝ := (negativeParams.p + Real.sqrt (negativeParams.p ^ 2 - 4 * negativeParams.q)) / 2
    (negativeParams.p : ℝ) * α ^ (3 - 2 : ℕ) ≤ lucasU negativeParams 3 ∧
      (lucasU negativeParams 3 : ℝ) ≤ α ^ (3 - 1 : ℕ) ∧
      (negativeParams.p : ℝ) * α ^ (3 - 1 : ℕ) ≤ lucasV negativeParams 3 ∧
      (lucasV negativeParams 3 : ℝ) ≤ α ^ (3 + 1 : ℕ) / negativeParams.p := by
  have hU : lucasU negativeParams 3 = 13 := by decide
  have hV : lucasV negativeParams 3 = 63 := by decide
  have hd : Real.sqrt (negativeParams.p ^ 2 - 4 * negativeParams.q) = 5 := by
    rw [show (negativeParams.p : ℝ) ^ 2 - 4 * negativeParams.q = 5 ^ 2 by norm_num [negativeParams],
      Real.sqrt_sq (by norm_num)]
  dsimp only
  rw [hU, hV, hd]
  norm_num [negativeParams]

-- The roots are 4 and 1, so the two upper bounds use the nontrivial denominator 3.
example :
    let d : ℝ := Real.sqrt (positiveParams.p ^ 2 - 4 * positiveParams.q)
    let α : ℝ := (positiveParams.p + d) / 2
    (positiveParams.p : ℝ) * α ^ (3 - 2 : ℕ) ≤ lucasU positiveParams 3 ∧
      (lucasU positiveParams 3 : ℝ) ≤ α ^ (3 : ℕ) / d ∧
      α ^ (3 : ℕ) ≤ (lucasV positiveParams 3 : ℝ) ∧
      (lucasV positiveParams 3 : ℝ) ≤ α ^ (3 + 1 : ℕ) / d := by
  have hU : lucasU positiveParams 3 = 21 := by decide
  have hV : lucasV positiveParams 3 = 65 := by decide
  have hd : Real.sqrt (positiveParams.p ^ 2 - 4 * positiveParams.q) = 3 := by
    rw [show (positiveParams.p : ℝ) ^ 2 - 4 * positiveParams.q = 3 ^ 2 by norm_num [positiveParams],
      Real.sqrt_sq (by norm_num)]
  dsimp only
  rw [hU, hV, hd]
  norm_num [positiveParams]

-- API check: extract the positive-parameter U bound at the first allowed index.
example :
    let d : ℝ := Real.sqrt (positiveParams.p ^ 2 - 4 * positiveParams.q)
    let α : ℝ := (positiveParams.p + d) / 2
    (lucasU positiveParams 2 : ℝ) ≤ α ^ (2 : ℕ) / d :=
  (lucasU_lucasV_alpha_bounds positiveParams (by decide) (by decide) (by decide)
    (n := 2) (by decide)).2.2.1 (by decide)

end MetaMathlibExt
