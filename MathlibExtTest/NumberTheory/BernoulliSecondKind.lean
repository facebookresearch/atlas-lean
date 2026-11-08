/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKind
public import Mathlib.Tactic.NormNum

namespace MetaMathlibExtTest

example : MetaMathlibExt.bernoulliSecondPowerSeries
    = (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1))⁻¹ :=
  rfl

example (n : ℕ) : MetaMathlibExt.bernoulliSecond n
    = (n.factorial : ℚ) *
      (PowerSeries.coeff n) MetaMathlibExt.bernoulliSecondPowerSeries :=
  MetaMathlibExt.bernoulliSecond_eq n

private lemma invLogUnit_coeff_zero :
    PowerSeries.coeff 0
      (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1))⁻¹ = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_inv]
  simp

private lemma invLogUnit_coeff_one :
    PowerSeries.coeff 1
      (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1))⁻¹ = 1 / 2 := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, PowerSeries.coeff_mk,
    invLogUnit_coeff_zero]

private lemma invLogUnit_coeff_two :
    PowerSeries.coeff 2
      (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1))⁻¹ = -1 / 12 := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, PowerSeries.coeff_mk,
    invLogUnit_coeff_zero, invLogUnit_coeff_one]

example : MetaMathlibExt.bernoulliSecond 0 = 1 := by
  rw [MetaMathlibExt.bernoulliSecond_eq,
    MetaMathlibExt.bernoulliSecondPowerSeries_eq, invLogUnit_coeff_zero]
  norm_num

example : MetaMathlibExt.bernoulliSecond 1 = 1 / 2 := by
  rw [MetaMathlibExt.bernoulliSecond_eq,
    MetaMathlibExt.bernoulliSecondPowerSeries_eq, invLogUnit_coeff_one]
  norm_num

example : MetaMathlibExt.bernoulliSecond 2 = -1 / 6 := by
  rw [MetaMathlibExt.bernoulliSecond_eq,
    MetaMathlibExt.bernoulliSecondPowerSeries_eq, invLogUnit_coeff_two]
  norm_num

example : MetaMathlibExt.bernoulliSecond 2 / (Nat.factorial 2 : ℚ) =
    -∑ k ∈ Finset.range 2,
      (MetaMathlibExt.bernoulliSecond k / (k.factorial : ℚ)) *
        ((-1 : ℚ) ^ (2 - k) / (2 - k + 1)) :=
  MetaMathlibExt.bernoulliSecond_div_factorial_eq 2 (by norm_num)

end MetaMathlibExtTest
