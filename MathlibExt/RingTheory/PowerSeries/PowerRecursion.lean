/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Power recursion for coefficients of formal power series

Multiplying a formal derivative by `X` weights each coefficient by its degree.
Applying this to two powers of the same series gives the power recursion identity.
-/

open PowerSeries

namespace MetaMathlibExt

/-- **Power recursion lemma for positive exponents.** Let $K$ be a field of characteristic zero,
let $A \in K[[X]]$ be a formal power series, and let $u$ and $v$ be positive integers. Write
$a_u(k)$ and $a_v(k)$ for the coefficients of $X^k$ in $A^u$ and $A^v$. Then for every natural
number $n$,

$$\sum_{k=0}^{n} \left(n - \left(\frac{u}{v} + 1\right) k\right) a_u(n-k)\, a_v(k) = 0.$$

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 17
(`jis-2024-24.1.6-lem-17`). -/
public theorem power_coeff_convolution_pow {K : Type*} [Field K] [CharZero K]
    (A : PowerSeries K) (u v : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((n : K) - ((u : K) / v + 1) * k) * coeff (n - k) (A ^ u) * coeff k (A ^ v) = 0 := by
  have hcoeff (B : PowerSeries K) (i : ℕ) :
      coeff i (X * derivative B) = (i : K) * coeff i B := by
    cases i with
    | zero => simp
    | succ i => rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_succ, mul_comm]
  have hpow : (v : PowerSeries K) * (A ^ v * (X * derivative (A ^ u))) =
      (u : PowerSeries K) * ((X * derivative (A ^ v)) * A ^ u) := by
    rw [derivative_pow, derivative_pow]
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv
    simp only [Nat.succ_sub_one, pow_succ]
    ring
  have h := congrArg (coeff n) hpow
  simp only [coeff_natCast_mul] at h
  calc
    _ = coeff n (A ^ v * (X * derivative (A ^ u))) -
        ((u : K) / v) * coeff n ((X * derivative (A ^ v)) * A ^ u) := by
      rw [coeff_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hcoeff, Nat.cast_sub (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      ring
    _ = 0 := by
      apply sub_eq_zero.mpr
      rw [div_mul_eq_mul_div, eq_div_iff (Nat.cast_ne_zero.mpr hv), mul_comm _ (v : K)]
      exact h

end MetaMathlibExt
