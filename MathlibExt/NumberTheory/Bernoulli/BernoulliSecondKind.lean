/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

namespace MetaMathlibExt

@[expose] public section

/-- Exponential generating function of the Bernoulli numbers of the
second kind: `t / log (1 + t) = ∑ₙ Bₙ^* * t ^ n / n!`, written as the
inverse of the unit series `log (1 + t) / t = ∑ₙ (-1) ^ n * t ^ n / (n + 1)`
(the logarithm itself is not a unit, having zero constant coefficient). -/
public noncomputable def bernoulliSecondPowerSeries : PowerSeries ℚ :=
  (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1))⁻¹

/-- Bernoulli number of the second kind `Bₙ^*`: `n!` times coefficient
`n` of `bernoulliSecondPowerSeries`, i.e. the
exponential-generating-function normalization of
`t / log (1 + t) = ∑ₙ Bₙ^* * t ^ n / n!` (Roman's normalization;
`B₀^* = 1`, `B₁^* = 1 / 2`, `B₂^* = -1 / 6`). -/
public noncomputable def bernoulliSecond (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * (PowerSeries.coeff n) bernoulliSecondPowerSeries

/-- Interface restatement of `bernoulliSecondPowerSeries`. -/
public theorem bernoulliSecondPowerSeries_eq :
    bernoulliSecondPowerSeries =
      (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1))⁻¹ :=
  rfl

/-- Interface restatement of `bernoulliSecond`. -/
public theorem bernoulliSecond_eq (n : ℕ) :
    bernoulliSecond n =
      (n.factorial : ℚ) * (PowerSeries.coeff n) bernoulliSecondPowerSeries :=
  rfl

/-- The defining EGF identity: `bernoulliSecondPowerSeries` times the
unit series `∑ₙ (-1) ^ n * t ^ n / (n + 1)` (which is `log (1 + t) / t`)
equals `1`. -/
public theorem bernoulliSecondPowerSeries_mul_mk :
    bernoulliSecondPowerSeries *
        (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1)) = 1 :=
  PowerSeries.inv_mul_cancel _ (by simp)

/-- Characteristic coefficient identity for
`bernoulliSecondPowerSeries`, from `bernoulliSecondPowerSeries_mul_mk`:
the Cauchy product of its coefficients with `(-1) ^ n / (n + 1)` is the
Kronecker delta at `0`. -/
public theorem sum_antidiagonal_bernoulliSecondPowerSeries_coeff (n : ℕ) :
    (∑ x ∈ Finset.antidiagonal n,
      (PowerSeries.coeff x.1) bernoulliSecondPowerSeries *
        ((-1 : ℚ) ^ x.2 / (x.2 + 1))) = if n = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff n) bernoulliSecondPowerSeries_mul_mk
  rw [PowerSeries.coeff_mul] at h
  simpa [PowerSeries.coeff_mk, PowerSeries.coeff_one] using h

/-- Coefficient recurrence for `bernoulliSecond` at positive indices,
from `sum_antidiagonal_bernoulliSecondPowerSeries_coeff` with the
`k = n` term isolated:
`Bₙ^* / n! = -∑_{k < n} (Bₖ^* / k!) * ((-1) ^ (n - k) / (n - k + 1))`. -/
public theorem bernoulliSecond_div_factorial_eq (n : ℕ) (hn : 1 ≤ n) :
    bernoulliSecond n / (n.factorial : ℚ) =
      -∑ k ∈ Finset.range n, (bernoulliSecond k / (k.factorial : ℚ)) *
        ((-1 : ℚ) ^ (n - k) / (n - k + 1)) := by
  have h := sum_antidiagonal_bernoulliSecondPowerSeries_coeff n
  rw [if_neg (show n ≠ 0 by omega)] at h
  have hsplit : (∑ x ∈ Finset.antidiagonal n,
        (PowerSeries.coeff x.1) bernoulliSecondPowerSeries *
          ((-1 : ℚ) ^ x.2 / (x.2 + 1))) =
      (PowerSeries.coeff n) bernoulliSecondPowerSeries +
        ∑ k ∈ Finset.range n, (PowerSeries.coeff k) bernoulliSecondPowerSeries *
          ((-1 : ℚ) ^ (n - k) / (n - k + 1)) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b : ℕ => (PowerSeries.coeff a) bernoulliSecondPowerSeries *
        ((-1 : ℚ) ^ b / (b + 1))) n, Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, Nat.cast_zero, zero_add, div_one,
      mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.cast_sub (Finset.mem_range.mp hk).le]
  rw [hsplit] at h
  have hcoeff : ∀ k : ℕ, (PowerSeries.coeff k) bernoulliSecondPowerSeries =
      bernoulliSecond k / (k.factorial : ℚ) := fun k => by
    rw [bernoulliSecond_eq]
    field_simp
  rw [hcoeff n] at h
  rw [Finset.sum_congr rfl (fun k _ => by rw [hcoeff k])] at h
  linarith

end

end MetaMathlibExt
