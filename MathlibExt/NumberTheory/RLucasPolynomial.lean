/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination

/-!
# The r-Lucas polynomials

The initial values and recurrence of the r-Lucas polynomials give a formula for their partial sums.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The $r$-Lucas polynomials of type $s$.** Let $R$ be a commutative semiring, let $r$ and $s$
be natural numbers and let $x, y \in R$. The $r$-Lucas polynomials of type $s$ are the sequence
$V_n = V^{(r,s)}_n(x, y)$, $n \ge 0$, of elements of $R$ given by $V_0 = s + 1$, $V_k = x^k$ for
$1 \le k \le r$, and $V_{n+1} = x V_n + y V_{n-r}$ for $n \ge r$.

The paper takes $1 \le s \le r$; the definition makes sense for every natural number $s$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public def rLucasPolynomial {R : Type*} [CommSemiring R] (r s : ℕ) (x y : R) : ℕ → R
  | 0 => (s : R) + 1
  | n + 1 =>
    if n < r then x ^ (n + 1)
    else x * rLucasPolynomial r s x y n + y * rLucasPolynomial r s x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- **Initial value of the $r$-Lucas polynomials.** For every commutative semiring $R$, all natural
numbers $r$ and $s$ and all $x, y \in R$, the $r$-Lucas polynomial of type $s$ satisfies
$V^{(r,s)}_0(x, y) = s + 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rLucasPolynomial_zero {R : Type*} [CommSemiring R] (r s : ℕ) (x y : R) :
    rLucasPolynomial r s x y 0 = (s : R) + 1 := by
  rw [rLucasPolynomial]

/-- **Initial values of the $r$-Lucas polynomials.** Let $R$ be a commutative semiring, let $s$ be
a natural number, let $x, y \in R$, and let $n < r$ be natural numbers. Then the $r$-Lucas
polynomial of type $s$ satisfies $V^{(r,s)}_{n+1}(x, y) = x^{n+1}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rLucasPolynomial_succ_of_lt {R : Type*} [CommSemiring R] {r n : ℕ} (s : ℕ)
    (x y : R) (h : n < r) : rLucasPolynomial r s x y (n + 1) = x ^ (n + 1) := by
  rw [rLucasPolynomial]
  simp [h]

/-- **Recurrence for the $r$-Lucas polynomials.** Let $R$ be a commutative semiring, let $s$ be a
natural number, let $x, y \in R$, and let $r \le n$ be natural numbers. Then the $r$-Lucas
polynomials of type $s$, $V_m = V^{(r,s)}_m(x, y)$, satisfy $V_{n+1} = x \, V_n + y \, V_{n-r}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rLucasPolynomial_succ_of_le {R : Type*} [CommSemiring R] {r n : ℕ} (s : ℕ)
    (x y : R) (h : r ≤ n) :
    rLucasPolynomial r s x y (n + 1)
      = x * rLucasPolynomial r s x y n + y * rLucasPolynomial r s x y (n - r) := by
  rw [rLucasPolynomial]
  simp [show ¬n < r by omega]

/-- **Sum of the first $n$ $r$-Lucas polynomials.** Let $K$ be a field, let $r \ge 1$ and $s$ be
natural numbers, let $x, y \in K$ with $1 - x - y \ne 0$, and write $V_j$ for the $r$-Lucas
polynomial of type $s$, $V_j = V^{(r,s)}_j(x, y)$. Then for every natural number $n$ with
$n \ge 1$ and $n \ge r - 1$,
$$
\sum_{j=1}^{n} V_j = \frac{1 + s y - V_{n+1} - y \sum_{j=1}^{r} V_{n-r+j}}{1 - x - y} - 1.
$$

The paper states $n \ge 1$; for $n < r - 1$ the right side involves $V$ at negative indices.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 4 (`integers-2025-A38-cor-4`). -/
public theorem sum_rLucasPolynomial {K : Type*} [Field K] {r n : ℕ} (hr : 1 ≤ r)
    (hn1 : 1 ≤ n) (hn : r ≤ n + 1) (s : ℕ) (x y : K) (hP : 1 - x - y ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, rLucasPolynomial r s x y j
      = (1 + s * y - rLucasPolynomial r s x y (n + 1)
          - y * ∑ j ∈ Finset.Icc 1 r, rLucasPolynomial r s x y (n + j - r))
        / (1 - x - y) - 1 := by
  let V := rLucasPolynomial r s x y
  let S (m : ℕ) := ∑ j ∈ Finset.range m, V j
  have hpow {j : ℕ} (hj : 0 < j) (hjr : j ≤ r) : V j = x ^ j := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    exact rLucasPolynomial_succ_of_lt s x y (by omega)
  have hinit : S r - s = ∑ j ∈ Finset.range r, x ^ j := by
    rw [show S r = _ from Finset.sum_range_eq_add_Ico V hr,
      Finset.sum_range_eq_add_Ico (fun j => x ^ j) hr, pow_zero,
      show V 0 = _ from rLucasPolynomial_zero r s x y]
    have h : ∑ j ∈ Finset.Ico 1 r, V j = ∑ j ∈ Finset.Ico 1 r, x ^ j :=
      Finset.sum_congr rfl fun j hj => hpow (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2.le
    rw [h, add_assoc, add_sub_cancel_left]
  -- Summing across the initial powers gives the base case. Each step adds one recurrence.
  have balance (k : ℕ) : (S (r + k) - s) * (1 - x) = 1 - V (r + k) + y * S k := by
    induction k with
    | zero => simp [hinit, hpow hr le_rfl, geom_sum_mul_neg, S]
    | succ k ih =>
      have hrec : V (r + k + 1) = x * V (r + k) + y * V k := by
        simpa [V] using rLucasPolynomial_succ_of_le (n := r + k) s x y (by omega : r ≤ r + k)
      have hstep (m : ℕ) : S (m + 1) = S m + V m := Finset.sum_range_succ V m
      rw [Nat.add_succ, hstep, hstep, hrec]
      linear_combination ih
  let k := n + 1 - r
  have hk : k + r = n + 1 := Nat.sub_add_cancel hn
  -- The last r terms form the difference of two prefix sums.
  have htail : ∑ j ∈ Finset.Icc 1 r, V (n + j - r) = S (n + 1) - S k := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      ← hk, show S (k + r) = _ from Finset.sum_range_add V k r, add_sub_cancel_left]
    exact Finset.sum_congr rfl fun j _ => congrArg V (by omega)
  have htotal : ∑ j ∈ Finset.Icc 1 n, V j = S (n + 1) - ((s : K) + 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sub V (show 1 ≤ n + 1 from hn1.trans (Nat.le_succ n)),
      Finset.sum_range_one, show V 0 = _ from rLucasPolynomial_zero r s x y]
  change (∑ j ∈ Finset.Icc 1 n, V j) = (1 + s * y - V (n + 1)
    - y * ∑ j ∈ Finset.Icc 1 r, V (n + j - r)) / (1 - x - y) - 1
  rw [htotal, htail, eq_sub_iff_add_eq, eq_div_iff hP]
  have h := balance k
  rw [Nat.add_comm r k, hk] at h
  linear_combination h

end

end MetaMathlibExt
