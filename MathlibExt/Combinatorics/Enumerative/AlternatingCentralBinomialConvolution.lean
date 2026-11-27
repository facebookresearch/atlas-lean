/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Central
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Ring

/-!
# Alternating central binomial convolution

The central binomial generating series is `(1 - 4X)^(-1/2)`. Multiplying it by
its value at `-X` gives `(1 - 16X²)^(-1/2)`: both sides have the same square
and constant term `1`.
-/

namespace MetaMathlibExt

open Finset PowerSeries

-- The central binomial series evaluated at `aX`.
private noncomputable def centralSeries (a : ℚ) : ℚ⟦X⟧ :=
  rescale a (rescale (-4) (binomialSeries ℚ (-1 / 2 : ℚ)))

private theorem coeff_centralSeries (a : ℚ) (n : ℕ) :
    coeff n (centralSeries a) = a ^ n * (n.centralBinom : ℚ) := by
  simp only [centralSeries, coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]
  congr 1
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ n ih =>
    have hchoose : ((n : ℚ) + 1) * Ring.choose (-1 / 2 : ℚ) (n + 1) =
        Ring.choose (-1 / 2 : ℚ) n * (-1 / 2 - n) := by
      simpa [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_add] using
        Ring.choose_smul_choose (-1 / 2 : ℚ) (Nat.le_succ n)
    have hcentral : ((n : ℚ) + 1) * ((n + 1).centralBinom : ℚ) =
        2 * (2 * (n : ℚ) + 1) * (n.centralBinom : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    apply mul_left_cancel₀ (show (n : ℚ) + 1 ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
    calc
      _ = (-4 : ℚ) ^ n * (-4) * (((n : ℚ) + 1) * Ring.choose (-1 / 2 : ℚ) (n + 1)) := by
        rw [pow_succ]
        ring
      _ = 2 * (2 * (n : ℚ) + 1) * ((-4 : ℚ) ^ n * Ring.choose (-1 / 2 : ℚ) n) := by
        rw [hchoose]
        ring
      _ = _ := by rw [ih, ← hcentral]

private theorem constantCoeff_centralSeries (a : ℚ) :
    constantCoeff (centralSeries a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_centralSeries, pow_zero, one_mul,
    Nat.centralBinom_zero, Nat.cast_one]

private theorem centralSeries_sq (a : ℚ) :
    centralSeries a ^ 2 * (1 - C (4 * a) * X) = 1 := by
  let B := binomialSeries ℚ (-1 / 2 : ℚ)
  have hB : B ^ 2 * (1 + X) = 1 := by
    have hone : binomialSeries ℚ (1 : ℚ) = 1 + X := by
      simpa only [Nat.cast_one, pow_one] using (binomialSeries_nat (R := ℚ) (A := ℚ) 1)
    rw [sq, ← hone, show B = binomialSeries ℚ (-1 / 2 : ℚ) from rfl,
      ← binomialSeries_add, show (-1 / 2 : ℚ) + (-1 / 2) = -1 by norm_num,
      ← binomialSeries_add, neg_add_cancel, binomialSeries_zero]
  have h := congrArg (rescale (-4 * a)) hB
  simpa only [centralSeries, rescale_rescale, B, map_mul, map_pow, map_add, map_one,
    rescale_X, neg_mul, map_neg, ← sub_eq_add_neg] using h

private theorem centralSeries_mul_neg :
    centralSeries (-1) * centralSeries 1 = expand 2 two_ne_zero (centralSeries 4) := by
  let H := centralSeries (-1) * centralSeries 1
  let D := expand 2 two_ne_zero (centralSeries 4)
  let Q : ℚ⟦X⟧ := 1 - C 16 * X ^ 2
  have hH : H ^ 2 * Q = 1 := calc
    _ = (centralSeries (-1) ^ 2 * (1 - C (4 * -1) * X)) *
        (centralSeries 1 ^ 2 * (1 - C (4 * 1) * X)) := by
      dsimp only [H, Q]
      simp only [mul_neg, mul_one, map_neg]
      rw [show (16 : ℚ) = 4 * 4 by norm_num, map_mul]
      ring
    _ = 1 := by rw [centralSeries_sq, centralSeries_sq, one_mul]
  have hD : D ^ 2 * Q = 1 := by
    simpa only [D, Q, show (4 : ℚ) * 4 = 16 by norm_num, map_mul, map_pow,
      map_sub, map_one, expand_C, expand_X] using
      congrArg (expand 2 two_ne_zero (R := ℚ)) (centralSeries_sq 4)
  have hsq : H ^ 2 = D ^ 2 :=
    mul_right_cancel₀ (fun hz => by rw [hz, mul_zero] at hD; exact zero_ne_one hD)
      (hH.trans hD.symm)
  have hprod : (H + D) * (H - D) = 0 := by
    rw [← sq_sub_sq, hsq, sub_self]
  have hsum : H + D ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    simp only [H, D, map_add, map_mul, map_zero, constantCoeff_expand,
      constantCoeff_centralSeries, one_mul] at hc
    norm_num at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hsum)

/-- **Alternating convolution of central binomial coefficients.** For every natural number
$n$, the integer $\sum_{k=0}^{n} (-1)^k \binom{2k}{k} \binom{2(n-k)}{n-k}$ equals
$2^n \binom{n}{n/2}$ when $n$ is even and $0$ when $n$ is odd.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 3 (`integers-2026-A19-thm-3`). -/
public theorem sum_neg_one_pow_centralBinom_mul_centralBinom (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * ((2 * k).choose k : ℤ) * ((2 * (n - k)).choose (n - k)) =
      if Even n then 2 ^ n * (n.choose (n / 2) : ℤ) else 0 := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  have h := congrArg (coeff n) centralSeries_mul_neg
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (centralSeries (-1)) * coeff j (centralSeries 1)), coeff_expand] at h
  simp only [coeff_centralSeries, one_pow, one_mul, Nat.centralBinom_eq_two_mul_choose] at h
  simp only [← even_iff_two_dvd] at h
  rw [h]
  by_cases hn : Even n
  · simp only [hn, ite_true]
    obtain ⟨m, rfl⟩ := hn.two_dvd
    rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2), pow_mul]
    norm_num
  · simp only [hn, ite_false]

end MetaMathlibExt
