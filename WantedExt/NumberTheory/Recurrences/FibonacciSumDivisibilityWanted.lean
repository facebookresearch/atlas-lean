/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On the divisibility of sums of Fibonacci numbers

Statements from Oisín Flynn-Connolly, "On the Divisibility
of Sums of Fibonacci Numbers", *INTEGERS* 25 (2025), Article A87
(<https://math.colgate.edu/~integers/z87/z87.pdf>).

The paper's Proposition 1, `S n = F (n + 2) - 1`, is already
Mathlib's `Nat.fib_succ_eq_succ_sum`, so it is not re-requested
here.  The Pisano period is the minimal period of the Fibonacci
pair step on `ZMod n × ZMod n` at `(0, 1)`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

/-- **Pisano period.** For a natural number $n$, the Pisano period $\pi(n)$ is the minimal period
of the pair $(0, 1)$ under the Fibonacci step $(a, b) \mapsto (b, a + b)$ on
$\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}$: the least $k \ge 1$ such that $k$
applications of the step map $(0, 1)$ back to $(0, 1)$, or $0$ if there is no such $k$ (as for
$n = 0$, where $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$). -/
noncomputable def pisanoPeriod (n : ℕ) : ℕ :=
  Function.minimalPeriod
    (fun p : ZMod n × ZMod n => (p.2, p.1 + p.2)) (0, 1)

/-- **The Pisano period of $F_n$ divides $2n$ for even $n$.** Let $F_n$ denote the $n$-th Fibonacci
number and $\pi(m)$ the Pisano period of $m$. For every even natural number $n > 1$, $\pi(F_n)$
divides $2n$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Proposition 2. -/
theorem_wanted pisanoPeriod_fib_dvd_two_mul
    (n : ℕ) (hn : 1 < n) (hn2 : 2 ∣ n) :
    pisanoPeriod (Nat.fib n) ∣ 2 * n

/-- **The minimum of $\pi(n)/n$ over $1 \le n < N$ tends to zero.** Let $\pi(n)$ denote the Pisano
period of $n$. As $N \to \infty$, the minimum of the real numbers $\pi(n)/n$ over the integers
$1 \le n \le N - 1$ (defined for $N \ge 2$) tends to $0$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Corollary 1. -/
theorem_wanted tendsto_iInf_pisanoPeriod_div_atTop
    :
    Filter.Tendsto
      (fun N : ℕ =>
        ⨅ n : {n : ℕ // n ∈ Finset.Icc 1 (N - 1)},
          (pisanoPeriod n.1 : ℝ) / n.1)
      Filter.atTop (nhds 0)

/-- **Sum of the first $p$ Fibonacci numbers modulo a prime $p$.** Let $p > 5$ be a prime, let
$F_i$ denote the $i$-th Fibonacci number, with $F_1 = F_2 = 1$, and let
$S = F_1 + F_2 + \dots + F_p$. If $p \equiv 1$ or $4 \pmod 5$, then $S$ leaves remainder $1$ on
division by $p$; if $p \equiv 2$ or $3 \pmod 5$, then $S$ leaves remainder $p - 2$ on division
by $p$; and in every case $p$ does not divide $S$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Theorem 1. -/
theorem_wanted sum_fib_mod_prime_eq_and_not_dvd
    (p : ℕ) (hp : p.Prime) (hp5 : 5 < p) :
    ((p % 5 = 1 ∨ p % 5 = 4) →
        (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = 1) ∧
      ((p % 5 = 2 ∨ p % 5 = 3) →
        (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = p - 2) ∧
      ¬p ∣ (∑ i ∈ Finset.Icc 1 p, Nat.fib i)

/-- **Odd Fibonacci numbers $F_n$ with $F_{F_n + 2} \equiv 1 \pmod{F_n}$.** Let $F_m$ denote the
$m$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. If $p$ is an odd prime with
$p \equiv 2 \pmod 3$ and $p \equiv 2$ or $3 \pmod 5$, and $n = 2p$ or $n = 4p$, then $F_n$ is odd
and $F_{F_n + 2}$ leaves remainder $1$ on division by $F_n$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Theorem 2. -/
theorem_wanted fib_two_mul_prime_odd_and_fib_fib_add_two_mod
    (p n : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1)
    (hp3 : p % 3 = 2) (hp5 : p % 5 = 2 ∨ p % 5 = 3)
    (hn : n = 2 * p ∨ n = 4 * p) :
    Nat.fib n % 2 = 1 ∧
      Nat.fib (Nat.fib n + 2) % Nat.fib n = 1

/-- **Infinitely many odd $k$ divide the sum of the first $k$ Fibonacci numbers.** Let $F_i$ denote
the $i$-th Fibonacci number, with $F_1 = F_2 = 1$. There are infinitely many odd positive integers
$k$ such that $k$ divides $F_1 + F_2 + \dots + F_k$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Corollary 2. -/
theorem_wanted infinite_setOf_odd_dvd_sum_fib
    :
    {k : ℕ | Odd k ∧ k ∣ (∑ i ∈ Finset.Icc 1 k, Nat.fib i)}.Infinite

end MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted
