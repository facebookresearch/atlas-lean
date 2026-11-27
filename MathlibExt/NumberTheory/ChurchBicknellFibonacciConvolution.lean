/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

namespace MetaMathlibExt

@[expose] public section

open Real
open scoped goldenRatio

/-- **The square root of 5 is nonzero.** The real square root $\sqrt{5}$ is not equal to $0$.

This is used to clear the denominators in Binet's formula. -/
theorem sqrt5_ne : √5 ≠ (0 : ℝ) :=
  Real.sqrt_ne_zero'.mpr (by norm_num)

theorem cb_lucas_zero : lucasNumber 0 = 2 := by decide

theorem cb_lucas_one : lucasNumber 1 = 1 := by decide

theorem cb_lucas_add_two (n : ℕ) :
    lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber n := by
  simp [lucasNumber]

/-- **Binet's formula for the Lucas numbers.** For every natural number $n$,
$\varphi^n + \psi^n = L_n$ as real numbers, where $\varphi = (1 + \sqrt{5})/2$ is the golden ratio,
$\psi = (1 - \sqrt{5})/2$ is its conjugate, and $L_n$ is the $n$-th Lucas number. -/
theorem cb_lucas_binet (n : ℕ) : φ ^ n + ψ ^ n = (lucasNumber n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [pow_zero, pow_zero, cb_lucas_zero, Nat.cast_ofNat]
      norm_num
  | one =>
      rw [pow_one, pow_one, goldenRatio_add_goldenConj, cb_lucas_one,
        Nat.cast_one]
  | more n ih1 ih2 =>
      have eα : φ ^ (n + 2) = φ ^ (n + 1) + φ ^ n := by
        calc φ ^ (n + 2) = φ ^ n * φ ^ 2 := by rw [pow_add]
          _ = φ ^ n * (φ + 1) := by rw [goldenRatio_sq]
          _ = φ ^ (n + 1) + φ ^ n := by rw [mul_add, mul_one, ← pow_succ]
      have eβ : ψ ^ (n + 2) = ψ ^ (n + 1) + ψ ^ n := by
        calc ψ ^ (n + 2) = ψ ^ n * ψ ^ 2 := by rw [pow_add]
          _ = ψ ^ n * (ψ + 1) := by rw [goldenConj_sq]
          _ = ψ ^ (n + 1) + ψ ^ n := by rw [mul_add, mul_one, ← pow_succ]
      have key : (φ ^ (n + 1) + φ ^ n) + (ψ ^ (n + 1) + ψ ^ n)
          = (φ ^ (n + 1) + ψ ^ (n + 1)) + (φ ^ n + ψ ^ n) := by
        ring
      have hL : lucasNumber (n + 1) + lucasNumber n = lucasNumber (n + 2) :=
        (cb_lucas_add_two n).symm
      rw [eα, eβ, key, ih1, ih2, ← Nat.cast_add, hL]

/-- **Church–Bicknell convolution over the reals.** For every natural number $n$,
$$\sum_{k=0}^{n} \binom{n}{k} F_k F_{n-k} = \frac{2^n L_n - 2}{5}$$
holds as an identity of real numbers, where $F_k$ is the $k$-th Fibonacci number and $L_n$ is
the $n$-th Lucas number. -/
theorem cb_keyR (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ)) =
      ((2 : ℝ) ^ n * (lucasNumber n : ℝ) - 2) / 5 := by
  have hD : ∀ k, φ ^ k - ψ ^ k = √5 * (Nat.fib k : ℝ) := by
    intro k
    have h1 : (φ ^ k - ψ ^ k) = (Nat.fib k : ℝ) * √5 :=
      (div_eq_iff sqrt5_ne).mp (coe_fib_eq k).symm
    rw [mul_comm]
    exact h1
  have hsq5 : √5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have h5 : ∀ k ∈ Finset.range (n + 1),
      5 * ((Nat.choose n k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ))
      = (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
        * (φ ^ (n - k) - ψ ^ (n - k)) := by
    intro k _
    rw [hD k, hD (n - k)]
    calc 5 * ((n.choose k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ))
          = ((n.choose k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ)) * 5 := by
            ring
      _ = ((n.choose k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ)) * √5 ^ 2 := by
            rw [hsq5]
      _ = (n.choose k : ℝ) * (√5 * (Nat.fib k : ℝ))
            * (√5 * (Nat.fib (n - k) : ℝ)) := by
            ring
  have hsum : 5 * (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ))
      = ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
          * (φ ^ (n - k) - ψ ^ (n - k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl h5
  have h2c : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have sA : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * φ ^ n)
      = 2 ^ n * φ ^ n := by
    rw [← Finset.sum_mul, h2c]
  have sD : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * ψ ^ n)
      = 2 ^ n * ψ ^ n := by
    rw [← Finset.sum_mul, h2c]
  have sB : (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * φ ^ k * ψ ^ (n - k))
      = (φ + ψ) ^ n := by
    have h := add_pow φ ψ n
    rw [h]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have sC : (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * ψ ^ k * φ ^ (n - k))
      = (φ + ψ) ^ n := by
    have h := add_pow ψ φ n
    rw [add_comm ψ φ] at h
    rw [h]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have e1 : ∀ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
        * (φ ^ (n - k) - ψ ^ (n - k))
      = (Nat.choose n k : ℝ) * φ ^ n
        - (Nat.choose n k : ℝ) * φ ^ k * ψ ^ (n - k)
        - (Nat.choose n k : ℝ) * ψ ^ k * φ ^ (n - k)
        + (Nat.choose n k : ℝ) * ψ ^ n := by
    intro k hk
    have hkn : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hkn' : k + (n - k) = n := by omega
    have eα : φ ^ k * φ ^ (n - k) = φ ^ n := by
      rw [← pow_add, hkn']
    have eβ : ψ ^ k * ψ ^ (n - k) = ψ ^ n := by
      rw [← pow_add, hkn']
    have eDD : (φ ^ k - ψ ^ k) * (φ ^ (n - k) - ψ ^ (n - k))
        = φ ^ n - φ ^ k * ψ ^ (n - k) - ψ ^ k * φ ^ (n - k)
          + ψ ^ n := by
      linear_combination eα + eβ
    calc (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
            * (φ ^ (n - k) - ψ ^ (n - k))
          = (Nat.choose n k : ℝ)
            * ((φ ^ k - ψ ^ k) * (φ ^ (n - k) - ψ ^ (n - k))) := by
            ring
      _ = (Nat.choose n k : ℝ) * (φ ^ n - φ ^ k * ψ ^ (n - k)
            - ψ ^ k * φ ^ (n - k) + ψ ^ n) := by
            rw [eDD]
      _ = (Nat.choose n k : ℝ) * φ ^ n
            - (Nat.choose n k : ℝ) * φ ^ k * ψ ^ (n - k)
            - (Nat.choose n k : ℝ) * ψ ^ k * φ ^ (n - k)
            + (Nat.choose n k : ℝ) * ψ ^ n := by
            ring
  have hsum2 : (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
          * (φ ^ (n - k) - ψ ^ (n - k)))
      = 2 ^ n * (φ ^ n + ψ ^ n) - 2 := by
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, sA, sB, sC, sD, goldenRatio_add_goldenConj]
    simp only [one_pow]
    ring
  have hL := cb_lucas_binet n
  rw [eq_div_iff (by norm_num : (5 : ℝ) ≠ 0)]
  have h2 := hsum
  rw [hsum2, hL] at h2
  linear_combination h2

/-- **Church–Bicknell Fibonacci binomial convolution.** For every natural number $n$,
$$\sum_{k=0}^{n} \binom{n}{k} F_k F_{n-k} = \frac{2^n L_n - 2}{5}$$
holds as an identity of rational numbers, where $F_k$ is the $k$-th Fibonacci number and $L_n$
is the $n$-th Lucas number.

Source: Ira M. Gessel and Ishan Kar, "Binomial Convolutions for Rational Power
Series," Journal of Integer Sequences 27 (2024), Article 24.1.3, equation
`e-cb1` (attributed there to C. A. Church and Marjorie Bicknell, "Exponential
generating functions for Fibonacci identities," Fibonacci Quarterly 11 (1973),
275–281). The proof follows the Binet-form computation in the JIS article:
with `φ`, `ψ` the golden ratio and its conjugate, expand
`(φ^k - ψ^k)(φ^(n-k) - ψ^(n-k))` and evaluate the four resulting binomial sums
by the binomial theorem.
Proves `Wanted` entry `church_bicknell_fibonacci_convolution`. -/
theorem church_bicknell_fibonacci_convolution (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℚ) * Nat.fib k * Nat.fib (n - k)) =
      (((2 : ℚ) ^ n * lucasNumber n - 2) / 5) := by
  refine Rat.cast_injective (α := ℝ) ?_
  push_cast
  exact cb_keyR n

end

end MetaMathlibExt
