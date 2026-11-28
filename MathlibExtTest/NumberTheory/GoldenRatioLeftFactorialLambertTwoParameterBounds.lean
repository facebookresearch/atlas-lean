/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertTwoParameterBounds

/-! # Tests for the two-parameter Lambert bounds -/

namespace MathlibExtTest.NumberTheory.GoldenRatioLeftFactorialLambertTwoParameterBounds

open MetaMathlibExt

-- The endpoint `n = 5`, `m = 1` recovers the unit-width interval below `34`.
example (A : ℝ) (hA : 4 ≤ A)
    (hW : lambertMap (-A / 4) = -(1 / 4) * (4 / 7 : ℝ) ^ (1 / 4 : ℝ)) :
    33 < kurepaPartialIntegral 5 A ∧ kurepaPartialIntegral 5 A < 34 := by
  have hb := kurepaPartialIntegral_lambertSequence_two_bounds 5 1 (by decide) le_rfl A
    (by norm_num; exact hA) (by norm_num at hW ⊢; exact hW)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  exact ⟨by linarith [hb.2], hb.1⟩

-- The same `n` with `m = 2` gives a strictly narrower half-unit interval.
example (A : ℝ) (hA : 4 ≤ A)
    (hW : lambertMap (-A / 4) = -(1 / 4) * (4 / 14 : ℝ) ^ (1 / 4 : ℝ)) :
    67 / 2 < kurepaPartialIntegral 5 A ∧ kurepaPartialIntegral 5 A < 34 := by
  have hb := kurepaPartialIntegral_lambertSequence_two_bounds 5 2 (by decide) (by decide) A
    (by norm_num; exact hA) (by norm_num; norm_num at hW; exact hW)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  exact ⟨by linarith [hb.2], hb.1⟩

end MathlibExtTest.NumberTheory.GoldenRatioLeftFactorialLambertTwoParameterBounds
