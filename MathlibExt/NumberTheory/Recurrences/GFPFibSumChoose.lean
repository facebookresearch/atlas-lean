/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Tactic.Ring

/-!
# Binomial expansion of Fibonacci-type generalized Fibonacci polynomials

`gfp_fib_eq_sum_choose` gives the explicit sum for the sequence with initial values zero and one.
-/

namespace MetaMathlibExt

open Polynomial Finset

namespace gfp_fib_eq_sum_choose

private noncomputable def term (d g : ℤ[X]) (m i : ℕ) : ℤ[X] :=
  ((m - i).choose i : ℤ[X]) * d ^ (m - 2 * i) * g ^ i

private theorem term_add_two (d g : ℤ[X]) (m i : ℕ) :
    term d g (m + 2) (i + 1) = d * term d g (m + 1) (i + 1) + g * term d g m i := by
  unfold term
  by_cases hi : m < 2 * i
  · simp only [Nat.choose_eq_zero_of_lt (show m + 2 - (i + 1) < i + 1 by omega),
      Nat.choose_eq_zero_of_lt (show m + 1 - (i + 1) < i + 1 by omega),
      Nat.choose_eq_zero_of_lt (show m - i < i by omega), Nat.cast_zero, zero_mul, mul_zero,
      add_zero]
  · rw [show m + 2 - (i + 1) = m - i + 1 by omega, Nat.choose_succ_succ', Nat.cast_add,
        show m + 1 - (i + 1) = m - i by omega, show m + 2 - 2 * (i + 1) = m - 2 * i by omega]
    by_cases he : m = 2 * i
    · rw [Nat.choose_eq_zero_of_lt (show m - i < i + 1 by omega), Nat.cast_zero, pow_succ g]
      ring
    · rw [show m - 2 * i = m + 1 - 2 * (i + 1) + 1 by omega, pow_succ d, pow_succ g]
      ring

-- Allow any upper bound containing the support, so the two preceding sums can be aligned.
private theorem sum_eq (d g : ℤ[X]) (m k : ℕ) (hk : m / 2 ≤ k) :
    generalizedFibonacciPolynomial 0 1 d g (m + 1) = ∑ i ∈ range (k + 1), term d g m i := by
  induction m using Nat.twoStepInduction generalizing k with
  | zero => rw [sum_range_succ']; simp [term]
  | one => rw [sum_range_succ']; simp [term, generalizedFibonacciPolynomial]
  | more m ih₀ ih₁ =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [generalizedFibonacciPolynomial_add_two 0 1 d g (m + 1), ih₁ (k + 1) (by omega),
      ih₀ k (by omega), sum_range_succ' (term d g (m + 1)) (k + 1),
      sum_range_succ' (term d g (m + 2)) (k + 1)]
    simp only [term_add_two, sum_add_distrib, ← mul_sum, mul_add]
    simp [term, pow_succ, mul_comm, add_comm, add_left_comm]

end gfp_fib_eq_sum_choose

/-- **Explicit formula for Fibonacci-type generalized Fibonacci polynomials.** Let $d$ and $g$ be
polynomials with integer coefficients, and let $F_n$ be the generalized Fibonacci polynomials
defined by $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = d F_{n+1} + g F_n$. Then for every $n \ge 1$,
$$F_n = \sum_{i=0}^{\lfloor (n-1)/2 \rfloor} \binom{n-i-1}{i} d^{n-2i-1} g^i.$$

The source quotes this formula from Flórez and Saunders.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.1 (1) (`fq-2024-florez11012023-lem-3.1`). -/
public theorem gfp_fib_eq_sum_choose (d g : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) :
    generalizedFibonacciPolynomial 0 1 d g n =
      ∑ i ∈ range ((n - 1) / 2 + 1),
        ((n - i - 1).choose i : ℤ[X]) * d ^ (n - 2 * i - 1) * g ^ i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Nat.sub_right_comm _ _ 1, Nat.succ_sub_one, gfp_fib_eq_sum_choose.term] using
    gfp_fib_eq_sum_choose.sum_eq d g m (m / 2) le_rfl

end MetaMathlibExt
