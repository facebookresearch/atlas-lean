/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.RLucasPolynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Alternating sums of the r-Lucas polynomials

This file proves `sum_neg_one_pow_mul_rLucasPolynomial`, the closed form of the alternating sum
$\sum_{j=1}^{n} (-1)^j V^{(r,s)}_j(x, y)$ of the $r$-Lucas polynomials of type $s$ for
$n \ge r - 1$.

The proof reduces it to the plain partial sum `sum_rLucasPolynomial`. Scaling the initial values
and the recurrence gives $m^j V^{(r,s)}_j(x, y) = V^{(r,s)}_j(m x, m^{r+1} y)$ for every $m$, so at
$m = -1$ the alternating sum is a plain partial sum of the $r$-Lucas polynomials at
$(-x, (-1)^{r+1} y)$. The case $n = 0$, which forces $r = 1$ and is not covered by
`sum_rLucasPolynomial`, is checked directly.
-/

namespace MetaMathlibExt

/-- **Scaling the $r$-Lucas polynomials.** For $m, x, y$ in a commutative semiring and every
natural number $j$, $V^{(r,s)}_j(m x, m^{r+1} y) = m^j V^{(r,s)}_j(x, y)$. -/
private theorem rLucasPolynomial_mul_mul_pow {R : Type*} [CommSemiring R] (r s : ℕ)
    (m x y : R) (j : ℕ) :
    rLucasPolynomial r s (m * x) (m ^ (r + 1) * y) j = m ^ j * rLucasPolynomial r s x y j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | j
    · simp [rLucasPolynomial_zero]
    rcases lt_or_ge j r with h | h
    · rw [rLucasPolynomial_succ_of_lt _ _ _ h, rLucasPolynomial_succ_of_lt _ _ _ h, mul_pow]
    · rw [rLucasPolynomial_succ_of_le _ _ _ h, rLucasPolynomial_succ_of_le _ _ _ h,
        ih j (by omega), ih (j - r) (by omega)]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [Nat.add_sub_cancel_left]
      ring

/-- **Alternating sum of $r$-Lucas polynomials.** Let $K$ be a field, let $r \ge 1$ and $s$ be
natural numbers, let $x, y \in K$ with $1 + x + (-1)^r y \ne 0$, and write $V_j$ for the
$r$-Lucas polynomial of type $s$, $V_j = V^{(r,s)}_j(x, y)$. Then for every natural number
$n \ge r - 1$,
$$
\sum_{j=1}^{n} (-1)^j V_j =
\frac{1 - (-1)^r s y + (-1)^n V_{n+1} + (-1)^r y \sum_{j=1}^{r} (-1)^{n-r+j} V_{n-r+j}}
{1 + x + (-1)^r y} - 1.
$$

For $n < r - 1$ the right side involves $V$ at negative indices.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 5 (`integers-2025-A38-cor-5`). -/
public theorem sum_neg_one_pow_mul_rLucasPolynomial {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n + 1) (s : ℕ) (x y : K) (hP : 1 + x + (-1) ^ r * y ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, (-1) ^ j * rLucasPolynomial r s x y j
      = (1 - (-1) ^ r * s * y + (-1) ^ n * rLucasPolynomial r s x y (n + 1)
          + (-1) ^ r * y * ∑ j ∈ Finset.Icc 1 r,
              (-1) ^ (n + j - r) * rLucasPolynomial r s x y (n + j - r))
        / (1 + x + (-1) ^ r * y) - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · -- For `n = 0` the sum is empty, `r = 1`, and the numerator equals the denominator.
    obtain rfl : r = 1 := by omega
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, eq_sub_iff_add_eq, zero_add, eq_comm,
      div_eq_one_iff_eq hP]
    norm_num [rLucasPolynomial_zero, rLucasPolynomial_succ_of_lt (r := 1) (n := 0)]
    ring
  · -- The terms `(-1) ^ j * V j` are the `r`-Lucas polynomials at `(-x, (-1) ^ (r + 1) * y)`.
    have hden : 1 - (-1) * x - (-1) ^ (r + 1) * y = 1 + x + (-1) ^ r * y := by ring
    have h := sum_rLucasPolynomial hr hn1 hn s ((-1) * x) ((-1) ^ (r + 1) * y) (hden ▸ hP)
    simp only [rLucasPolynomial_mul_mul_pow, hden] at h
    rw [h]
    congr 2
    ring

end MetaMathlibExt
