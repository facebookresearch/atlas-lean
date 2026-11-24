/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Power recursion for integer powers of a unit formal power series

Comparing the logarithmic derivatives of two integer powers gives a weighted
convolution identity for their coefficients.
-/

open PowerSeries

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Power recursion lemma for nonzero integer exponents.** Let $K$ be a field of characteristic
zero, let $A$ be an invertible formal power series in $K[[X]]$, and let $u$ and $v$ be nonzero
integers. Write $a_u(k)$ and $a_v(k)$ for the coefficients of $X^k$ in $A^u$ and $A^v$. Then for
every natural number $n$,

$$\sum_{k=0}^{n} \left(n - \left(\frac{u}{v} + 1\right) k\right) a_u(n-k)\, a_v(k) = 0.$$

Invertibility of $A$ is assumed so that the negative powers $A^u$, $A^v$ make sense.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 17
(`jis-2024-24.1.6-lem-17`). -/
public theorem power_coeff_convolution_zpow {K : Type*} [Field K] [CharZero K]
    (A : (PowerSeries K)ˣ) (u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((n : K) - ((u : K) / v + 1) * k) *
        coeff (n - k) ((A ^ u : (PowerSeries K)ˣ) : PowerSeries K) *
        coeff k ((A ^ v : (PowerSeries K)ˣ) : PowerSeries K) = 0 := by
  -- The logarithmic derivative takes products of units to sums.
  let L : (PowerSeries K)ˣ →* Multiplicative (PowerSeries K) :=
    { toFun := fun B ↦ Multiplicative.ofAdd (↑B⁻¹ * derivative (B : PowerSeries K))
      map_one' := by
        change ↑(1 : (PowerSeries K)ˣ)⁻¹ * derivative (1 : PowerSeries K) = 0
        simp
      map_mul' := by
        intro B C
        change ↑(B * C)⁻¹ * derivative ((B * C : (PowerSeries K)ˣ) : PowerSeries K) =
          ↑B⁻¹ * derivative (B : PowerSeries K) + ↑C⁻¹ * derivative (C : PowerSeries K)
        simp only [mul_inv_rev, Units.val_mul, Derivation.leibniz, smul_eq_mul, mul_add]
        calc
          _ = (↑B⁻¹ * ↑B) * (↑C⁻¹ * derivative (C : PowerSeries K)) +
              (↑C⁻¹ * ↑C) * (↑B⁻¹ * derivative (B : PowerSeries K)) := by ring
          _ = _ := by simp [add_comm] }
  have hderiv (z : ℤ) : derivative (↑(A ^ z) : PowerSeries K) =
      (z : PowerSeries K) * ↑(A ^ z) * (L A).toAdd := by
    have h := congrArg Multiplicative.toAdd (map_zpow L A z)
    change ↑(A ^ z)⁻¹ * derivative (↑(A ^ z) : PowerSeries K) = z • (L A).toAdd at h
    rw [Units.inv_mul_eq_iff_eq_mul, zsmul_eq_mul] at h
    rw [h]
    ring
  let F (z : ℤ) : PowerSeries K := ↑(A ^ z)
  have hpow : (v : PowerSeries K) * (F v * (X * derivative (F u))) =
      (u : PowerSeries K) * ((X * derivative (F v)) * F u) := by
    dsimp only [F]
    rw [hderiv, hderiv]
    ring
  have hcoeff (B : PowerSeries K) (i : ℕ) :
      coeff i (X * derivative B) = (i : K) * coeff i B := by
    cases i with
    | zero => simp
    | succ i => rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_succ, mul_comm]
  calc
    _ = coeff n (F v * (X * derivative (F u))) -
        ((u : K) / v) * coeff n ((X * derivative (F v)) * F u) := by
      rw [coeff_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hcoeff, Nat.cast_sub (Nat.le_of_lt_succ (Finset.mem_range.mp hk)), F]
      ring
    _ = 0 := by
      apply sub_eq_zero.mpr
      rw [div_mul_eq_mul_div, eq_div_iff (Int.cast_ne_zero.mpr hv), mul_comm _ (v : K)]
      simpa only [coeff_intCast_mul] using congrArg (coeff n) hpow

end MetaMathlibExt
