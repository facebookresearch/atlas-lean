/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.HalfIntegerHarmonic
import Mathlib.Tactic.NormNum

/-! # Tests for harmonic numbers of half-integer index -/

open MetaMathlibExt

-- At `k = 0`, the first two evaluations reduce to the unshifted half-integer values.
example : Complex.digamma (1 / 2) + Real.eulerMascheroniConstant = -2 * Complex.log 2 := by
  simpa using (harmonic_nat_sub_half_values 0).1

example :
    ∑' j : ℕ, (1 / ((j : ℂ) + 1) ^ 2 - 1 / ((j : ℂ) + 1 / 2) ^ 2) = -2 * riemannZeta 2 := by
  simpa using (harmonic_nat_sub_half_values 0).2.1

example :
    ∑' j : ℕ, (1 / ((j : ℂ) + 1) ^ 3 - 1 / ((j : ℂ) + 1 / 2) ^ 3) = -6 * riemannZeta 3 :=
  (harmonic_nat_sub_half_values 0).2.2.1

-- The exponent-one difference still converges, although neither tail alone is summable.
example :
    ∑' j : ℕ, (1 / ((j : ℂ) + 1 / 2) - 1 / ((j : ℂ) + 1 + 1 / 2)) = 2 := by
  simpa [Finset.sum_range_one] using (harmonic_nat_sub_half_values 1).2.2.2 0

-- A nonempty odd sum at exponent two contributes `4 * (1 + 1 / 9)`.
example :
    ∑' j : ℕ, (1 / ((j : ℂ) + 1) ^ 2 - 1 / ((j : ℂ) + 2 + 1 / 2) ^ 2) =
      -2 * riemannZeta 2 + 40 / 9 := by
  norm_num [Finset.sum_range_succ] at *
  have h := (harmonic_nat_sub_half_values 2).2.1
  norm_num [Finset.sum_range_succ] at h
  exact h
