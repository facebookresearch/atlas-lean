/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.GFPFibSumChoose
import Mathlib.Tactic.Ring

/-!
# Binomial expansion of Lucas-type generalized Fibonacci polynomials

Subtracting `d * F_n` from `2 * F_{n+1}` gives the normalized Lucas sequence. The two
Fibonacci expansions then combine by Pascal's identity, giving an exact natural quotient.
-/

namespace MetaMathlibExt

open Polynomial Finset

private theorem normalized_lucas_eq {α p₀ : ℤ} (hα : α * p₀ = 2) {p₁ d : ℤ[X]}
    (hd : d = C α * p₁) (g : ℤ[X]) (n : ℕ) :
    C α * generalizedFibonacciPolynomial (C p₀) p₁ d g n =
      2 * generalizedFibonacciPolynomial 0 1 d g (n + 1) -
        d * generalizedFibonacciPolynomial 0 1 d g n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [generalizedFibonacciPolynomial_zero, generalizedFibonacciPolynomial_one,
      generalizedFibonacciPolynomial_zero, ← C_mul, hα]
    simp
  | one =>
    rw [generalizedFibonacciPolynomial_one, generalizedFibonacciPolynomial_add_two 0 1 d g 0,
      generalizedFibonacciPolynomial_one, generalizedFibonacciPolynomial_zero, ← hd]
    ring
  | more n ih₀ ih₁ =>
    rw [generalizedFibonacciPolynomial_add_two (C p₀) p₁ d g n, mul_add,
      mul_left_comm (C α) d, mul_left_comm (C α) g, ih₀, ih₁,
      generalizedFibonacciPolynomial_add_two 0 1 d g (n + 1),
      generalizedFibonacciPolynomial_add_two 0 1 d g n]
    ring

-- Clear the denominator in ℕ before passing to polynomial coefficients.
private theorem lucas_choose_quotient_add (n i : ℕ) (hn : 1 ≤ n) (hi : 2 * i ≤ n) :
    n * (n - i).choose i / (n - i) + (n - i - 1).choose i =
      (n - i).choose i + (n - i).choose i := by
  cases i with
  | zero => simp [Nat.div_self (by omega : 0 < n)]
  | succ i =>
    have hk : 0 < n - (i + 1) := by omega
    have hpascal := Nat.choose_succ_right (n - (i + 1)) i hk
    have hmul : (n - (i + 1)) * (n - (i + 1) - 1).choose i =
        (n - (i + 1)).choose (i + 1) * (i + 1) := by
      have h := Nat.add_one_mul_choose_eq (n - (i + 1) - 1) i
      rwa [show n - (i + 1) - 1 + 1 = n - (i + 1) by omega] at h
    have hnumerator : n * (n - (i + 1)).choose (i + 1) =
        ((n - (i + 1)).choose (i + 1) + (n - (i + 1) - 1).choose i) * (n - (i + 1)) := calc
      _ = (n - (i + 1) + (i + 1)) * (n - (i + 1)).choose (i + 1) := by
        rw [show n - (i + 1) + (i + 1) = n by omega]
      _ = (n - (i + 1)) * (n - (i + 1)).choose (i + 1) +
          (n - (i + 1)).choose (i + 1) * (i + 1) := by
        rw [add_mul, Nat.mul_comm (i + 1)]
      _ = _ := by rw [← hmul, add_mul]; ac_rfl
    change _ / (n - (i + 1)) + _ = _
    rw [hnumerator, Nat.mul_div_cancel _ hk]
    omega

-- Align with the range for F_{n+1}; an extra endpoint of even n has zero coefficient.
private theorem d_mul_fib_eq_sum_choose (d g : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) :
    d * generalizedFibonacciPolynomial 0 1 d g n =
      ∑ i ∈ range (n / 2 + 1), ((n - i - 1).choose i : ℤ[X]) * d ^ (n - 2 * i) * g ^ i := by
  rw [gfp_fib_eq_sum_choose d g hn, mul_sum]
  let term (i : ℕ) := ((n - i - 1).choose i : ℤ[X]) * d ^ (n - 2 * i) * g ^ i
  calc
    _ = ∑ i ∈ range ((n - 1) / 2 + 1), term i := by
      refine sum_congr rfl fun i hi ↦ ?_
      have hil := mem_range.mp hi
      dsimp [term]
      calc
        _ = ((n - i - 1).choose i : ℤ[X]) * d ^ (n - 2 * i - 1 + 1) * g ^ i := by
          rw [pow_succ]
          ring
        _ = _ := by rw [show n - 2 * i - 1 + 1 = n - 2 * i by omega]
    _ = ∑ i ∈ range (n / 2 + 1), term i := by
      refine sum_subset (range_mono (by omega)) fun i _ hi ↦ ?_
      simp only [mem_range] at hi
      simp [term, Nat.choose_eq_zero_of_lt (show n - i - 1 < i by omega)]

/-- **Explicit formula for Lucas-type generalized Fibonacci polynomials.** Let $\alpha$ and $p_0$
be integers with $\alpha p_0 = 2$, let $p_1$ and $g$ be polynomials with integer coefficients, and
put $d = \alpha p_1$. Let $L_n$ be the generalized Fibonacci polynomials defined by $L_0 = p_0$,
$L_1 = p_1$ and $L_{n+2} = d L_{n+1} + g L_n$. Then for every $n \ge 1$, writing
$c_i = \lfloor n \binom{n-i}{i} / (n-i) \rfloor$,
$$\alpha L_n = \sum_{i=0}^{\lfloor n/2 \rfloor} c_i \, d^{n-2i} g^i.$$

The quotient $n \binom{n-i}{i} / (n-i)$ is always an integer, so the floor does not change it;
the source writes the coefficient as $\frac{n}{n-i} \binom{n-i}{i}$ and quotes the formula from
Flórez and Saunders.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.1 (2) (`fq-2024-florez11012023-lem-3.1`). -/
public theorem gfp_lucas_eq_sum_choose {α p₀ : ℤ} (hα : α * p₀ = 2) {p₁ d : ℤ[X]}
    (hd : d = C α * p₁) (g : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) :
    C α * generalizedFibonacciPolynomial (C p₀) p₁ d g n =
      ∑ i ∈ range (n / 2 + 1),
        ((n * (n - i).choose i / (n - i) : ℕ) : ℤ[X]) * d ^ (n - 2 * i) * g ^ i := by
  rw [normalized_lucas_eq hα hd, gfp_fib_eq_sum_choose d g (n := n + 1) (by omega),
    d_mul_fib_eq_sum_choose d g hn, Nat.add_sub_cancel, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  have hil := mem_range.mp hi
  have hcoeff := congrArg (fun k : ℕ ↦ (k : ℤ[X]))
    (lucas_choose_quotient_add n i hn (by omega))
  simp only [Nat.cast_add] at hcoeff
  rw [show n + 1 - i - 1 = n - i by omega, show n + 1 - 2 * i - 1 = n - 2 * i by omega]
  calc
    _ = (((n - i).choose i : ℤ[X]) + ((n - i).choose i : ℤ[X]) -
        ((n - i - 1).choose i : ℤ[X])) * d ^ (n - 2 * i) * g ^ i := by ring
    _ = _ := by rw [← hcoeff]; ring

end MetaMathlibExt
