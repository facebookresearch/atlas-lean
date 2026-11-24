/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination

/-!
# The r-Fibonacci polynomials and their partial sums

This file defines the r-Fibonacci polynomials by their initial values and recurrence, identifies
the case `r = 1`, `x = y = 1` with the Fibonacci numbers, and proves the closed form
`sum_rFibonacciPolynomial` for the sum of the first `n` of them.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The $r$-Fibonacci polynomials.** Let $R$ be a commutative semiring, let $r$ be a natural
number and let $x, y \in R$. The $r$-Fibonacci polynomials $U^{(r)}_n(x, y) \in R$, $n \ge 0$, are
defined by $U^{(r)}_0 = 0$, $U^{(r)}_k = x^{k-1}$ for $1 \le k \le r$, and
$U^{(r)}_{n+1} = x \, U^{(r)}_n + y \, U^{(r)}_{n-r}$ for $n \ge r$.

These are the initial values and recurrence displayed for $\xi_n = m^{n-1} U_n$ in the paper,
at $m = 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public def rFibonacciPolynomial {R : Type*} [CommSemiring R] (r : ℕ) (x y : R) : ℕ → R
  | 0 => 0
  | n + 1 =>
    if n < r then x ^ n
    else x * rFibonacciPolynomial r x y n + y * rFibonacciPolynomial r x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- **The zeroth $r$-Fibonacci polynomial vanishes.** For every natural number $r$ and all
$x, y$ in a commutative semiring $R$, the $r$-Fibonacci polynomial $U^{(r)}_0(x, y)$ is $0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public theorem rFibonacciPolynomial_zero {R : Type*} [CommSemiring R] (r : ℕ) (x y : R) :
    rFibonacciPolynomial r x y 0 = 0 := by
  rw [rFibonacciPolynomial]

/-- **Initial values of the $r$-Fibonacci polynomials.** Let $R$ be a commutative semiring, let
$x, y \in R$, and let $n < r$ be natural numbers. Then the $r$-Fibonacci polynomial
$U^{(r)}_{n+1}(x, y)$ equals $x^n$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public theorem rFibonacciPolynomial_succ_of_lt {R : Type*} [CommSemiring R] {r n : ℕ}
    (x y : R) (h : n < r) : rFibonacciPolynomial r x y (n + 1) = x ^ n := by
  rw [rFibonacciPolynomial]
  simp [h]

/-- **Recurrence for the $r$-Fibonacci polynomials.** Let $R$ be a commutative semiring, let
$x, y \in R$, and let $r \le n$ be natural numbers. Then the $r$-Fibonacci polynomials
$U_m = U^{(r)}_m(x, y)$ satisfy $U_{n+1} = x \, U_n + y \, U_{n-r}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public theorem rFibonacciPolynomial_succ_of_le {R : Type*} [CommSemiring R] {r n : ℕ}
    (x y : R) (h : r ≤ n) :
    rFibonacciPolynomial r x y (n + 1)
      = x * rFibonacciPolynomial r x y n + y * rFibonacciPolynomial r x y (n - r) := by
  rw [rFibonacciPolynomial]
  simp [show ¬n < r by omega]

/-- **The $1$-Fibonacci polynomials at $x = y = 1$ are the Fibonacci numbers.** For every
natural number $n$, the $r$-Fibonacci polynomial with $r = 1$, evaluated at $x = y = 1$ in the
natural numbers, is the $n$-th Fibonacci number: $U^{(1)}_n(1, 1) = F_n$, where $F_0 = 0$,
$F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rFibonacciPolynomial_one_one_one :
    ∀ n, rFibonacciPolynomial 1 (1 : ℕ) 1 n = Nat.fib n
  | 0 => by rw [rFibonacciPolynomial_zero]; rfl
  | 1 => by rw [rFibonacciPolynomial_succ_of_lt _ _ (by omega)]; simp
  | n + 2 => by
    rw [rFibonacciPolynomial_succ_of_le _ _ (by omega), rFibonacciPolynomial_one_one_one (n + 1),
      show n + 1 - 1 = n by omega, rFibonacciPolynomial_one_one_one n, Nat.fib_add_two]
    ring

/-- **Sum of the first $n$ $r$-Fibonacci polynomials.** Let $K$ be a field, let $r \ge 1$ be a
natural number, let $x, y \in K$ with $1 - x - y \ne 0$, and write $U_j$ for the $r$-Fibonacci
polynomial $U^{(r)}_j(x, y)$. Then for every natural number $n$,
$$
\sum_{j=1}^{n} U_j = \frac{1 - U_{n+1} - y \sum_{j=1}^{r} U_{n-r+j}}{1 - x - y},
$$
where the terms of the inner sum with $n - r + j \le 0$ are zero.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 2 (`integers-2025-A38-cor-2`). -/
public theorem sum_rFibonacciPolynomial {K : Type*} [Field K] {r : ℕ} (hr : 1 ≤ r)
    (x y : K) (hP : 1 - x - y ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, rFibonacciPolynomial r x y j
      = (1 - rFibonacciPolynomial r x y (n + 1)
          - y * ∑ j ∈ Finset.Icc 1 r, rFibonacciPolynomial r x y (n + j - r))
        / (1 - x - y) := by
  rw [eq_div_iff hP]
  -- Extended by zero to the indices `m ≤ 0`, the recurrence holds from index one on.
  have hrec (m : ℕ) : rFibonacciPolynomial r x y (m + 1 + 1)
      = x * rFibonacciPolynomial r x y (m + 1) + y * rFibonacciPolynomial r x y (m + 1 - r) := by
    rcases lt_or_ge (m + 1) r with h | h
    · rw [rFibonacciPolynomial_succ_of_lt x y h, rFibonacciPolynomial_succ_of_lt x y (by omega),
        Nat.sub_eq_zero_of_le h.le, rFibonacciPolynomial_zero]
      ring
    · exact rFibonacciPolynomial_succ_of_le x y h
  -- Moving a window of indices up by one adds its new top term and drops its old bottom term.
  have hshift (f : ℕ → K) (k : ℕ) :
      ∑ j ∈ Finset.Icc 1 k, f (j + 1) = ∑ j ∈ Finset.Icc 1 k, f j + f (k + 1) - f 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
      ring
  induction n with
  | zero =>
    have h0 : ∑ j ∈ Finset.Icc 1 r, rFibonacciPolynomial r x y (0 + j - r) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [Nat.sub_eq_zero_of_le (by have := (Finset.mem_Icc.mp hj).2; omega),
          rFibonacciPolynomial_zero]
    rw [h0, rFibonacciPolynomial_succ_of_lt (n := 0) x y hr]
    simp
  | succ n ih =>
    -- The window of the last `r` indices moves up by one.
    have hwin : ∑ j ∈ Finset.Icc 1 r, rFibonacciPolynomial r x y (n + 1 + j - r)
        = ∑ j ∈ Finset.Icc 1 r, rFibonacciPolynomial r x y (n + j - r)
          + rFibonacciPolynomial r x y (n + 1) - rFibonacciPolynomial r x y (n + 1 - r) := by
      have h := hshift (fun i => rFibonacciPolynomial r x y (n + i - r)) r
      rw [show n + (r + 1) - r = n + 1 by omega] at h
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => by rw [show n + 1 + j - r = n + (j + 1) - r by omega]
    rw [Finset.sum_Icc_succ_top (by omega), hwin]
    linear_combination ih + hrec n

end

end MetaMathlibExt
