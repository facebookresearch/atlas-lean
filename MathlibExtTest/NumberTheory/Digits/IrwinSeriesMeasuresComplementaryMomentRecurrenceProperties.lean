/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresComplementaryMomentRecurrenceProperties
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Tests for complementary moment recurrence properties

The binary recurrence with omitted digit one has a constant initial row, first moment four
thirds in the next row, and first-moment limit one. Positive rows decrease with the degree.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Theorem 2.
-/

namespace MathlibExtTest.NumberTheory.Digits
namespace IrwinSeriesMeasuresComplementaryMomentRecurrenceProperties

open MetaMathlibExt Filter

example (v : ℕ → ℕ → ℝ) (hv : ComplementaryMomentRecurrence 2 1 v) :
    (∀ m, 1 ≤ m → v 0 m = 2) ∧ v 1 1 = 4 / 3 ∧
      Tendsto (fun j => v j 1) atTop (nhds 1) := by
  obtain ⟨h0, _, hdeg, _, hlim⟩ := complementaryMomentRecurrence_properties 2 1
    (by decide) (by decide) v hv
  have hconst (m : ℕ) (hm : 1 ≤ m) := (hdeg 0 m hm).1 ⟨rfl, rfl, rfl⟩
  refine ⟨hconst, ?_, ?_⟩
  · have he := hv.2 1 le_rfl 1
    norm_num [complementaryDigitPowerSum, digitPowerSum, Finset.sum_range_succ,
      hconst 1 le_rfl, h0] at he
    linarith
  · convert hlim 1 le_rfl using 2
    norm_num

example (v : ℕ → ℕ → ℝ) (hv : ComplementaryMomentRecurrence 2 1 v)
    (j m : ℕ) (hm : 1 ≤ m) : v (j + 1) (m + 1) < v (j + 1) m := by
  have h := complementaryMomentRecurrence_properties 2 1 (by decide) (by decide) v hv
  exact (h.2.2.1 (j + 1) m hm).2 (by omega)

end IrwinSeriesMeasuresComplementaryMomentRecurrenceProperties
end MathlibExtTest.NumberTheory.Digits
