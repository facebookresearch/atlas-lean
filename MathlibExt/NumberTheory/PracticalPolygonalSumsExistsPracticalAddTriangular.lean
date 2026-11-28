/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PolygonalNumber
public import MathlibExt.NumberTheory.PracticalNumber
import Mathlib.Data.Nat.Log
import MathlibExt.NumberTheory.ArithmeticFunction.SigmaTwoPow
import MathlibExt.NumberTheory.OddSquareTriangular
import MathlibExt.NumberTheory.PracticalPolygonalSums
import MathlibExt.NumberTheory.PracticalPolygonalSumsIsPracticalNumberMulOfLeSigmaAddOne

/-!
# Positive integers as sums of a practical number and a triangular number

For every natural number $n > 0$, there are a practical number $q$ and a natural number $k$
with $n = q + k(k+1)/2$, allowing $k = 0$. Following Somu and Tran, the proof chooses
$m = \lfloor \log_4(8n+1) \rfloor$ and a bounded square root of $8n+1$ modulo $2^{m+2}$.
The root gives the triangular summand, and the difference is a power of two times a factor
small enough for the product to be practical.

## References

* Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal Numbers*,
  Journal of Integer Sequences 27 (2024), Article 24.5.1, pp. 1–12, Theorem 1 and Lemmas 3–5 in §3.
* Sai Teja Somu, Ting Hon Stanford Li, and Andrzej Kukla, *On some results on practical numbers*,
  Integers 23 (2023), Article A68, pp. 1–9, Lemma 3.2 (the bounded square root).
* M. Margenstern, *Les nombres pratiques: théorie, observations et conjectures*,
  J. Number Theory 37 (1991), pp. 1–36, Corollary 1 (the small-factor multiplication rule).

The practical-power induction uses the same small-factor argument as `isPracticalNumber_primorial`
in `MathlibExt.NumberTheory.PracticalPolygonalSumsEventuallyTwo`. The divisor-sum calculation
uses `sigma_two_pow_add_one` from `MathlibExt.NumberTheory.ArithmeticFunction.SigmaTwoPow`.
-/

namespace MetaMathlibExt

open ArithmeticFunction
open scoped Nat

/-- **Every positive integer is a practical number plus a triangular number.** For every natural
number $n > 0$ there are a practical number $q$ and a natural number $k$ with
$n = q + k(k+1)/2$; the case $k = 0$, where the triangular number is $0$, is allowed.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Theorem 1
(`jis-2024-24.5.1-thm-1`). -/
public theorem exists_practical_add_triangular (n : ℕ) (hn : 0 < n) :
    ∃ q k : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber 3 k := by
  have hm : 0 < Nat.log 4 (8 * n + 1) :=
    Nat.le_log_of_pow_le (x := 1) (by decide) (by rw [pow_one]; omega)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let b : ℕ := 2 ^ j
  have hb4 : (4 : ℕ) ^ j = b ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, mul_comm 2 j, pow_mul]
  have hlo : 4 * b ^ 2 ≤ 8 * n + 1 := by
    have h := Nat.pow_log_le_self 4 (show 8 * n + 1 ≠ 0 by omega)
    rwa [hj, pow_succ', hb4] at h
  have hhi : 8 * n + 1 < 16 * b ^ 2 := by
    have h := Nat.lt_pow_succ_log_self (b := 4) (by decide) (8 * n + 1)
    rw [hj, pow_succ', pow_succ', hb4] at h
    omega
  obtain ⟨x, hxpos, hx, hmod⟩ := exists_sq_modEq_eight_mul_add_one j.succ n (Nat.succ_pos _) hn
  have hbpos : 0 < b := by positivity
  have hxlt : x < 2 * b := by
    rw [pow_succ'] at hx
    change x ≤ 2 * b - 1 at hx
    omega
  have hsqpos : 0 < x ^ 2 := pow_pos hxpos 2
  have hsq : x ^ 2 < 8 * n + 1 := by
    calc
      x ^ 2 < (2 * b) ^ 2 := Nat.pow_lt_pow_left hxlt (by decide)
      _ = 4 * b ^ 2 := by rw [mul_pow]; rfl
      _ ≤ _ := hlo
  obtain ⟨s, hs⟩ := (Nat.modEq_iff_dvd' hsq.le).mp hmod
  have hdiff : 8 * n + 1 - x ^ 2 = 8 * (b * s) := by
    rw [hs, show j.succ + 2 = j + 3 from rfl, pow_add]
    change b * 8 * s = _
    ac_rfl
  have hsum : x ^ 2 + 8 * (b * s) = 8 * n + 1 := by omega
  have hxodd : Odd x :=
    (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp (Nat.odd_iff.mpr (by omega))
  obtain ⟨k, hk⟩ := sq_sub_one_div_eight_eq_triangular x hxodd
  have hspos : 0 < s := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hdiff
    omega
  have hsle : s ≤ 2 * b := by
    have hprod : b * s ≤ b * (2 * b) := calc
      b * s ≤ n := by omega
      _ ≤ 2 * b ^ 2 := by omega
      _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hprod hbpos
  have hσ : sigma 1 b + 1 = 2 * b := by
    simpa only [b, pow_succ'] using sigma_two_pow_add_one j
  have hpractical (a : ℕ) : IsPracticalNumber (2 ^ a) := by
    induction a with
    | zero =>
      rw [pow_zero, isPracticalNumber_iff]
      refine ⟨by decide, fun u hu hle ↦ ?_⟩
      have : u = 1 := le_antisymm hle hu
      subst u
      exact ⟨{1}, by simp, by simp⟩
    | succ a ih =>
      rw [pow_succ]
      have hle := le_sigma_one (2 ^ a)
      have hpos : 0 < (2 : ℕ) ^ a := by positivity
      exact isPracticalNumber_mul_of_le_sigma_add_one _ 2 ih (by decide) (by omega)
  refine ⟨b * s, k,
    isPracticalNumber_mul_of_le_sigma_add_one b s (hpractical j) hspos (hσ ▸ hsle), ?_⟩
  omega

end MetaMathlibExt
