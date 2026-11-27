/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LurothBorelBernstein
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

open Filter MeasureTheory MetaMathlibExt

-- Exponential thresholds give a null set, even though the initial threshold is one.
example :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∃ᶠ n in atTop, (2 : ℝ) ^ n ≤ lurothDigitSeq x n} = 0 := by
  apply (volume_lurothDigit_ge_zero_one (fun n => (2 : ℝ) ^ n) (fun _ => by positivity)).1
  simpa [one_div, inv_pow] using summable_geometric_two

-- A threshold below one tests the full-measure case where reciprocal thresholds exceed one.
example :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∃ᶠ n in atTop, (1 / 2 : ℝ) ≤ lurothDigitSeq x n} = 1 := by
  apply (volume_lurothDigit_ge_zero_one (fun _ => (1 / 2 : ℝ)) (fun _ => by positivity)).2
  simp [summable_const_iff]

-- Linear growth is already slow enough for the threshold to be met infinitely often a.e.
example :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 |
      ∃ᶠ (n : ℕ) in atTop, (n : ℝ) + 1 ≤ lurothDigitSeq x n} = 1 := by
  apply (volume_lurothDigit_ge_zero_one (fun n => (n : ℝ) + 1) (fun _ => by positivity)).2
  simpa using mt (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)⁻¹) 1).1
    Real.not_summable_natCast_inv
