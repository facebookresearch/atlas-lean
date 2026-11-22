/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MedianGenocchiNumber
public import MathlibExt.NumberTheory.GenocchiNumber
public import Mathlib.NumberTheory.Bernoulli

/-!
# Genocchi numbers via Bernoulli numbers

The generating-function Genocchi numbers `genocchiNumber` satisfy `G n = 2 * (1 - 2 ^ n) * B n`,
which identifies them with the Bernoulli-formula representation `genocchiNumberViaBernoulli`.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem exp_sub_one_ne_zero : PowerSeries.exp ℚ - 1 ≠ 0 := by
  intro h0
  have hc : (PowerSeries.coeff 1) (PowerSeries.exp ℚ - 1) = 0 := by
    rw [h0]
    simp
  simp [map_sub, PowerSeries.coeff_exp] at hc

private theorem exp_add_one_ne_zero : PowerSeries.exp ℚ + 1 ≠ 0 := by
  intro h0
  have hc : PowerSeries.constantCoeff (PowerSeries.exp ℚ + 1) = 0 := by
    rw [h0]
    simp
  simp [map_add, PowerSeries.constantCoeff_exp] at hc

/-- The Genocchi power series `2 * x / (exp x + 1)` equals
`2 * x / (exp x - 1) - 4 * x / (exp (2 * x) - 1)`, i.e. `2 • B(x) - 2 • B(2 * x)` for the
Bernoulli power series `B`. -/
private theorem genocchiPowerSeries_eq_bernoulli :
    genocchiPowerSeries =
      2 • bernoulliPowerSeries ℚ - 2 • (PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) := by
  have hB : bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) = PowerSeries.X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hB2 : (PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * ((PowerSeries.exp ℚ) ^ 2 - 1)
      = 2 • PowerSeries.X := by
    have h := congrArg (fun x : PowerSeries ℚ => (PowerSeries.rescale 2) x) hB
    simp only [map_mul, map_sub, map_one] at h
    have hsq : (PowerSeries.exp ℚ) ^ 2 = (PowerSeries.rescale 2) (PowerSeries.exp ℚ) := by
      simpa using PowerSeries.exp_pow_eq_rescale_exp (A := ℚ) 2
    have hX : (PowerSeries.rescale 2) (PowerSeries.X : PowerSeries ℚ) = 2 • PowerSeries.X := by
      ext n
      by_cases hn : n = 1
      · subst hn
        simp [PowerSeries.coeff_X]
      · simp [PowerSeries.coeff_X, hn]
    rw [← hsq, hX] at h
    exact h
  have hG : genocchiPowerSeries * (PowerSeries.exp ℚ + 1) = 2 * PowerSeries.X := by
    rw [genocchiPowerSeries_eq, mul_assoc, PowerSeries.inv_mul_cancel]
    · ring
    · simp [map_add, PowerSeries.constantCoeff_exp]
  apply mul_right_cancel₀ exp_add_one_ne_zero
  rw [hG]
  apply mul_right_cancel₀ exp_sub_one_ne_zero
  calc 2 * PowerSeries.X * (PowerSeries.exp ℚ - 1)
      = 2 • (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) * (PowerSeries.exp ℚ + 1)
        - 2 • ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) *
          ((PowerSeries.exp ℚ) ^ 2 - 1)) := by
        rw [hB, hB2]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring
    _ = _ := by
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring

/-- **Genocchi numbers in terms of Bernoulli numbers.** For every natural number $n$, the Genocchi
number $G_n$, defined by $\frac{2x}{e^x + 1} = \sum_{m \ge 0} G_m \frac{x^m}{m!}$, satisfies
$G_n = 2(1 - 2^n) B_n$, where $B_n$ is the $n$-th Bernoulli number with the convention
$B_1 = -\tfrac{1}{2}$. -/
theorem genocchiNumber_eq_bernoulli (n : ℕ) :
    genocchiNumber n = 2 * (1 - (2 : ℚ) ^ n) * bernoulli n := by
  have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [genocchiNumber_eq, genocchiPowerSeries_eq_bernoulli, map_sub, map_nsmul, map_nsmul,
    PowerSeries.coeff_rescale]
  simp only [bernoulliPowerSeries, PowerSeries.coeff_mk, nsmul_eq_mul, Nat.cast_ofNat,
    Algebra.algebraMap_self, RingHom.id_apply]
  field_simp

/-- **The two definitions of the Genocchi numbers agree.** For every natural number $n$, the
rational number $2(1 - 2^n) B_n$, where $B_n$ is the $n$-th Bernoulli number with the convention
$B_1 = -\tfrac{1}{2}$, equals the Genocchi number $G_n$ defined by the exponential generating
function $\frac{2x}{e^x + 1} = \sum_{m \ge 0} G_m \frac{x^m}{m!}$. -/
theorem genocchiNumberViaBernoulli_eq_genocchiNumber (n : ℕ) :
    genocchiNumberViaBernoulli n = genocchiNumber n :=
  (genocchiNumber_eq_bernoulli n).symm

end MetaMathlibExt
