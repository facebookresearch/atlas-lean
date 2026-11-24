/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FiveCoreAnalogs
import Mathlib.Tactic.NormNum

open PowerSeries

namespace MetaMathlibExt.phiFiveCoreAnalog_five_pow_mul

private noncomputable abbrev theta := rescale (-1 : ℤ) (ramanujanThetaPow 1 1)

-- Compute the initial coefficients from the quotient with its denominator cleared.
private theorem initial_coefficients :
    phiFiveCoreAnalog 0 = 1 ∧ phiFiveCoreAnalog 1 = 2 ∧ phiFiveCoreAnalog 5 = 14 := by
  have ht : (ramanujanThetaPow 1 1).coeff 1 = 2 ∧ (ramanujanThetaPow 1 1).coeff 2 = 0 ∧
      (ramanujanThetaPow 1 1).coeff 3 = 0 ∧ (ramanujanThetaPow 1 1).coeff 4 = 2 ∧
      (ramanujanThetaPow 1 1).coeff 5 = 0 := by
    simp only [ramanujanThetaPow, coeff_mk]
    decide
  obtain ⟨t1, t2, t3, t4, t5⟩ := ht
  have h (n : ℕ) := congrArg (coeff n) mk_phiFiveCoreAnalog_mul
  change ∀ n, coeff n (mk phiFiveCoreAnalog * theta) =
    coeff n (expand 5 (by decide) theta ^ 5) at h
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_mk,
    ← map_pow, coeff_expand] at h
  have hc0 : constantCoeff (rescale (-1) (ramanujanThetaPow 1 1)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ramanujanThetaPow]
    simp
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  norm_num [theta, Finset.sum_range_succ, coeff_rescale, t1, t2, t3, t4, t5,
    coeff_zero_eq_constantCoeff_apply, coeff_one_pow, constantCoeff_ramanujanThetaPow, hc0]
    at h0 h1 h2 h3 h4 h5
  exact ⟨by omega, by omega, by omega⟩

example : phiFiveCoreAnalog 25 = 74 := by
  have h := phiFiveCoreAnalog_five_pow_mul (k := 2) (by decide) 1
  norm_num [initial_coefficients.2.1, initial_coefficients.2.2] at h
  exact h

example : phiFiveCoreAnalog 125 = 374 := by
  have h := phiFiveCoreAnalog_five_pow_mul (k := 3) (by decide) 1
  norm_num [initial_coefficients.2.1, initial_coefficients.2.2] at h
  exact h

end MetaMathlibExt.phiFiveCoreAnalog_five_pow_mul
