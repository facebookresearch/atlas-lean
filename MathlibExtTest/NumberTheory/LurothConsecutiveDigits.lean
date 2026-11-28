/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LurothConsecutiveDigits

open MeasureTheory MetaMathlibExt
open scoped ENNReal

namespace MathlibExtTest.NumberTheory.LurothConsecutiveDigits

-- First Lüroth digit at least 3: projection is monotone on `[2, ∞)`.
example :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 | (3 : ℝ) ≤ (lurothDigitSeq x 0 : ℝ)} ≤
      3 ^ (1 : ℕ) * ∫⁻ x in {x : Fin 1 → ℝ | (∀ i, 2 ≤ x i) ∧ (3 : ℝ) ≤ x 0},
        ENNReal.ofReal (∏ i, 1 / x i ^ 2) := by
  have hmono : MonotoneOn (fun x : Fin 1 → ℝ => x 0) {x | ∀ i, 2 ≤ x i} := by
    intro a _ b _ hab
    exact hab 0
  exact MetaMathlibExt.volume_lurothDigits_ge_le _ hmono _

-- Sum of the first two digits at least 5: coordinatewise sum is monotone.
example :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 |
      (5 : ℝ) ≤ (lurothDigitSeq x 0 : ℝ) + (lurothDigitSeq x 1 : ℝ)} ≤
      3 ^ (2 : ℕ) * ∫⁻ x in {x : Fin 2 → ℝ | (∀ i, 2 ≤ x i) ∧ (5 : ℝ) ≤ x 0 + x 1},
        ENNReal.ofReal (∏ i, 1 / x i ^ 2) := by
  have hmono : MonotoneOn (fun x : Fin 2 → ℝ => x 0 + x 1) {x | ∀ i, 2 ≤ x i} := by
    intro a _ b _ hab
    exact add_le_add (hab 0) (hab 1)
  exact MetaMathlibExt.volume_lurothDigits_ge_le _ hmono _

end MathlibExtTest.NumberTheory.LurothConsecutiveDigits
