/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import MathlibExt.Combinatorics.Enumerative.RStirlingSecond
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Stirling numbers from derivatives of powers of one minus the exponential

The derivatives at zero of `(1 - exp x) ^ k * exp (v * x)` give alternating binomial sums
expressed by ordinary and shifted Stirling numbers of the second kind.
-/

namespace MetaMathlibExt

open Finset

namespace iteratedDeriv_one_sub_exp_pow

private theorem deriv_eq_sum (k r v : ℕ) :
    iteratedDeriv r (fun x : ℝ => (1 - Real.exp x) ^ k * Real.exp (v * x)) 0 =
      ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * k.choose p * ((v + p : ℕ) : ℝ) ^ r := by
  have expand (x : ℝ) : (1 - Real.exp x) ^ k * Real.exp (v * x) =
      ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * k.choose p * Real.exp ((v + p : ℕ) * x) := by
    rw [show 1 - Real.exp x = -Real.exp x + 1 by ring, add_pow, sum_mul]
    apply sum_congr rfl
    intro p _
    rw [Nat.cast_add, add_mul, Real.exp_add, Real.exp_nat_mul x p, neg_pow]
    simp only [one_pow, mul_one]
    ring
  simp_rw [expand]
  rw [iteratedDeriv_fun_sum (by intros; fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul, mul_zero,
    Real.exp_zero, mul_one]

private theorem sum_eq_stirling (k r : ℕ) :
    ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * k.choose p * (p : ℝ) ^ r =
      (-1) ^ k * k.factorial * (Nat.stirlingSecond r k : ℝ) := by
  rw [mul_right_comm _ (k.factorial : ℝ), mul_assoc,
    stirlingSecond_mul_factorial_eq_sum, mul_sum]
  apply sum_congr rfl
  intro p hp
  have hp_le := Nat.le_of_lt_succ (mem_range.mp hp)
  have hsign : (-1 : ℝ) ^ k * (-1) ^ (k - p) = (-1) ^ p := by
    rw [← pow_add, show k + (k - p) = p + 2 * (k - p) by omega, pow_add, pow_mul]
    norm_num
  simp only [← mul_assoc, hsign]

private theorem sum_eq_rStirling (k r v : ℕ) :
    ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * k.choose p * ((v + p : ℕ) : ℝ) ^ r =
      (-1) ^ k * k.factorial * (rStirlingSecond (r + v) (k + v) v : ℝ) := by
  simp_rw [Nat.cast_add, add_pow (v : ℝ), mul_sum]
  rw [sum_comm, rStirlingSecond_add_add]
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  calc
    _ = (∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * k.choose p * (p : ℝ) ^ (r - i)) *
          ((v : ℝ) ^ i * r.choose i) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [sum_eq_stirling]; ring

end iteratedDeriv_one_sub_exp_pow

open iteratedDeriv_one_sub_exp_pow

/-- **Stirling numbers from derivatives of powers of one minus the exponential.** For all natural
numbers $k$, $r$ and $v$, write ${a \brace b}$ for the Stirling numbers of the second kind and
${a \brace b}_v$ for the r-Stirling numbers of the second kind with parameter $v$, and use the
convention $0^0 = 1$. Then the real functions $x \mapsto (1 - e^x)^k$ and
$x \mapsto (1 - e^x)^k e^{vx}$ satisfy
$$\frac{d^r}{dx^r} (1 - e^x)^k \Big|_{x=0} = \sum_{p=0}^{k} (-1)^p \binom{k}{p} p^r =
(-1)^k k! {r \brace k}$$
and
$$\frac{d^r}{dx^r} (1 - e^x)^k e^{vx} \Big|_{x=0} = \sum_{p=0}^{k} (-1)^p \binom{k}{p} (v+p)^r =
(-1)^k k! {r+v \brace k+v}_v.$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Lemma 1 (`integers-2026-A109-lem-1`). -/
public theorem iteratedDeriv_one_sub_exp_pow (k r v : ℕ) :
    (iteratedDeriv r (fun x : ℝ => (1 - Real.exp x) ^ k) 0 =
        ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * (k.choose p : ℝ) * (p : ℝ) ^ r ∧
      ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * (k.choose p : ℝ) * (p : ℝ) ^ r =
        (-1) ^ k * k.factorial * (Nat.stirlingSecond r k : ℝ)) ∧
    (iteratedDeriv r (fun x : ℝ => (1 - Real.exp x) ^ k * Real.exp (v * x)) 0 =
        ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * (k.choose p : ℝ) * ((v + p : ℕ) : ℝ) ^ r ∧
      ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * (k.choose p : ℝ) * ((v + p : ℕ) : ℝ) ^ r =
        (-1) ^ k * k.factorial * (rStirlingSecond (r + v) (k + v) v : ℝ)) := by
  refine ⟨⟨?_, sum_eq_stirling k r⟩, deriv_eq_sum k r v, sum_eq_rStirling k r v⟩
  simpa using deriv_eq_sum k r 0

end MetaMathlibExt
