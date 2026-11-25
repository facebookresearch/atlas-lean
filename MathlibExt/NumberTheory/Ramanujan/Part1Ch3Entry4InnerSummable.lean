/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 4

Absolute summability of (j+1)ⁿxʲ⁺¹/j!.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry4InnerSummable

/-- **Absolute convergence of Ramanujan's Bell-type series (Entry 4).** For every complex
number $x$ and every natural number $n$, the series
$\sum_{j=0}^{\infty} \frac{(j+1)^n x^{j+1}}{j!}$ converges absolutely.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 4, formula (4.1), printed
    pp. 47--48 / PDF pp. 57--58.
Proves `Wanted` entry `ramanujan_part1_ch3_entry4_inner_summable`.
-/
theorem ramanujan_part1_ch3_entry4_inner_summable (x : ℂ) (n : ℕ) :
    Summable (fun j : ℕ => ‖((j + 1 : ℂ) ^ n * x ^ (j + 1) / (Nat.factorial j : ℂ))‖) := by
  have hdom :
      Summable (fun j : ℕ => ‖x‖ * ((((2 : ℝ) ^ n) * ‖x‖) ^ j / (Nat.factorial j : ℝ))) := by
    have h := Real.summable_pow_div_factorial (((2 : ℝ) ^ n) * ‖x‖)
    exact h.mul_left ‖x‖
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) _ hdom
  intro j
  have hcast : ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) := by push_cast; ring
  have hnorm : ‖((j : ℂ) + 1) ^ n * x ^ (j + 1) / (Nat.factorial j : ℂ)‖
      = (((j : ℝ) + 1) ^ n * ‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ)) := by
    rw [hcast, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
      Complex.norm_natCast]
    push_cast
    ring
  have hnat : j + 1 ≤ 2 ^ j := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hreal : ((j : ℝ) + 1) ≤ (2 : ℝ) ^ j := by
    exact_mod_cast hnat
  have hpow : (((j : ℝ) + 1)) ^ n ≤ (((2 : ℝ) ^ j)) ^ n :=
    pow_le_pow_left₀ (by positivity) hreal n
  have hpow2 : ((((2 : ℝ) ^ j)) ^ n) = (((2 : ℝ) ^ n)) ^ j := by
    rw [← pow_mul, mul_comm j n, pow_mul]
  have hCs : ‖x‖ ^ (j + 1) = ‖x‖ * ‖x‖ ^ j := pow_succ' ‖x‖ j
  have hnum : (((j : ℝ) + 1)) ^ n * ‖x‖ ^ (j + 1)
      ≤ ‖x‖ * ((((2 : ℝ) ^ n) * ‖x‖) ^ j) := by
    rw [hCs, mul_pow]
    have h1 : (((j : ℝ) + 1)) ^ n ≤ (((2 : ℝ) ^ n)) ^ j := hpow2 ▸ hpow
    have h2 : (((j : ℝ) + 1)) ^ n * (‖x‖ * ‖x‖ ^ j)
        ≤ ((((2 : ℝ) ^ n)) ^ j) * (‖x‖ * ‖x‖ ^ j) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : ‖x‖ * (((2 : ℝ) ^ n) ^ j * ‖x‖ ^ j)
        = ((((2 : ℝ) ^ n)) ^ j) * (‖x‖ * ‖x‖ ^ j) := by ring
    rw [h3]
    exact h2
  rw [hnorm, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hnum (by positivity)

end Entry4InnerSummable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
