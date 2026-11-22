/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
public import MathlibExt.Combinatorics.Enumerative.RiordanNumber

namespace MetaMathlibExt

@[expose] public section

/-- **Log-convexity of the even-indexed Riordan numbers.** Let $r_n$ denote the $n$-th Riordan
number. The even-indexed Riordan numbers $r_0, r_2, r_4, \dots$ form a log-convex sequence: for
every natural number $n$,
$$r_{2n+2}^2 \le r_{2n} \, r_{2n+4}.$$

The Riordan numbers begin $1, 0, 1, 1, 3, 6, 15, \dots$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Corollary 1
(`integers-2026-A55-cor-1`). -/
public theorem_wanted riordanNumber_even_logConvex (n : ℕ) :
    riordanNumber (2 * (n + 1)) ^ 2 ≤
      riordanNumber (2 * n) * riordanNumber (2 * (n + 2))

/-- **Alternating sums of Motzkin numbers.** Let $M_k$ denote the $k$-th Motzkin number. For a
natural number $n$, the $n$-th alternating Motzkin sum is the integer
$$T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k.$$
It is OEIS A187306, which begins $1, 0, 2, 2, 7, 14, 37, \dots$

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (2). -/
public def motzkinAlternatingSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (motzkinNumber k : ℤ)

/-- **The alternating Motzkin sum at 0.** Let $M_k$ denote the $k$-th Motzkin number and let
$T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$. Then $T_0 = 1$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Table 2. -/
public theorem motzkinAlternatingSum_zero : motzkinAlternatingSum 0 = 1 := by
  simp [motzkinAlternatingSum, motzkinNumber_zero]

/-- **Recurrence for alternating Motzkin sums.** Let $M_k$ denote the $k$-th Motzkin number and
let $T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$. For every natural number $n$, $T_{n+1} = M_{n+1} - T_n$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (2). -/
public theorem motzkinAlternatingSum_succ (n : ℕ) :
    motzkinAlternatingSum (n + 1) = motzkinNumber (n + 1) - motzkinAlternatingSum n := by
  rw [motzkinAlternatingSum, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul,
    motzkinAlternatingSum, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

/-- **Alternating Motzkin sums at 1 and 2.** Let $M_k$ denote the $k$-th Motzkin number and let
$T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$. Then $T_1 = 0$ and $T_2 = 2$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Table 2. -/
public theorem motzkinAlternatingSum_one_two :
    motzkinAlternatingSum 1 = 0 ∧ motzkinAlternatingSum 2 = 2 := by
  have h1 : motzkinAlternatingSum 1 = 0 := by
    rw [motzkinAlternatingSum_succ, motzkinAlternatingSum_zero, motzkinNumber_one]; norm_num
  refine ⟨h1, ?_⟩
  rw [motzkinAlternatingSum_succ, h1, motzkinNumber_two]; norm_num

/-- **Alternating sums of Fibonacci numbers.** Let $F_k$ denote the $k$-th Fibonacci number,
with $F_0 = 0$ and $F_1 = 1$. For a natural number $n$, the $n$-th alternating Fibonacci sum is
the integer
$$W_n = \sum_{k=0}^{n} (-1)^{n-k} F_k.$$
The sequence begins $0, 1, 0, 2, 1, 4, 4, 9, \dots$

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (9). -/
public def fibonacciAlternatingSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (Nat.fib k : ℤ)

/-- **The alternating Fibonacci sum at 0.** Let $F_k$ denote the $k$-th Fibonacci number, with
$F_0 = 0$ and $F_1 = 1$, and let $W_n = \sum_{k=0}^{n} (-1)^{n-k} F_k$. Then $W_0 = 0$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Table 3. -/
public theorem fibonacciAlternatingSum_zero : fibonacciAlternatingSum 0 = 0 := by
  simp [fibonacciAlternatingSum]

/-- **Recurrence for alternating Fibonacci sums.** Let $F_k$ denote the $k$-th Fibonacci
number, with $F_0 = 0$ and $F_1 = 1$, and let $W_n = \sum_{k=0}^{n} (-1)^{n-k} F_k$. For every
natural number $n$, $W_{n+1} = F_{n+1} - W_n$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (9). -/
public theorem fibonacciAlternatingSum_succ (n : ℕ) :
    fibonacciAlternatingSum (n + 1) = Nat.fib (n + 1) - fibonacciAlternatingSum n := by
  rw [fibonacciAlternatingSum, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul,
    fibonacciAlternatingSum, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

/-- **The alternating Motzkin sums are eventually log-balanced and tempered.** Let $M_k$ denote
the $k$-th Motzkin number and let $T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$. For every natural
number $n \ge 9$,
$$T_n^2 \le T_{n-1} T_{n+1} \quad\text{and}\quad n T_{n-1} T_{n+1} \le (n+1) T_n^2,$$
and for every natural number $n \ge 6$,
$$n T_n^2 \le (n+1) T_{n-1} T_{n+1} \quad\text{and}\quad n T_{n-1} T_{n+1} \le (n+1) T_n^2.$$

Following Došlić, a positive sequence $(z_n)_{n \ge N}$ is log-balanced if it is log-convex,
$z_n^2 \le z_{n-1} z_{n+1}$, and $(z_n/n!)$ is log-concave, $n z_{n-1} z_{n+1} \le (n+1) z_n^2$,
for every $n \ge N + 1$; it is tempered if its quotients $x_n = z_{n+1}/z_n$ satisfy
$\frac{n}{n+1} x_{n-1} \le x_n \le \frac{n+1}{n} x_{n-1}$ for every $n \ge N + 1$. So the two
parts say that $(T_n)_{n \ge 8}$ is log-balanced and $(T_n)_{n \ge 5}$ is tempered, with the
inequalities cleared of denominators (all terms are positive here) and the factorials and
quotient weights using the original index $n$, as in the paper's proofs.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 1. -/
public theorem_wanted motzkinAlternatingSum_logBalanced_tempered :
    (∀ n, 9 ≤ n →
      motzkinAlternatingSum n ^ 2 ≤
          motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1) ∧
        n * (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1)) ≤
          (n + 1) * motzkinAlternatingSum n ^ 2) ∧
    (∀ n, 6 ≤ n →
      n * motzkinAlternatingSum n ^ 2 ≤
          (n + 1) * (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1)) ∧
        n * (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1)) ≤
          (n + 1) * motzkinAlternatingSum n ^ 2)

/-- **Products of consecutive alternating Motzkin sums are eventually log-convex and
log-balanced.** Let $M_k$ denote the $k$-th Motzkin number, let
$T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$ and let $P_n = T_n T_{n+1}$. For every natural number
$n \ge 7$, $P_n^2 \le P_{n-1} P_{n+1}$; and for every natural number $n \ge 10$,
$P_n^2 \le P_{n-1} P_{n+1}$ and $n P_{n-1} P_{n+1} \le (n+1) P_n^2$.

Following Došlić, a positive sequence $(z_n)_{n \ge N}$ is log-convex if
$z_n^2 \le z_{n-1} z_{n+1}$ for every $n \ge N + 1$, and log-balanced if moreover $(z_n/n!)$ is
log-concave, $n z_{n-1} z_{n+1} \le (n+1) z_n^2$, for every $n \ge N + 1$. So the two parts say
that $(P_n)_{n \ge 6}$ is log-convex and $(P_n)_{n \ge 9}$ is log-balanced.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 2. -/
public theorem_wanted motzkinAlternatingSum_mul_succ_logConvex_logBalanced :
    (∀ n, 7 ≤ n →
      (motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)) ^ 2 ≤
        (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum n) *
          (motzkinAlternatingSum (n + 1) * motzkinAlternatingSum (n + 2))) ∧
    (∀ n, 10 ≤ n →
      (motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)) ^ 2 ≤
          (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum n) *
            (motzkinAlternatingSum (n + 1) * motzkinAlternatingSum (n + 2)) ∧
        n * ((motzkinAlternatingSum (n - 1) * motzkinAlternatingSum n) *
            (motzkinAlternatingSum (n + 1) * motzkinAlternatingSum (n + 2))) ≤
          (n + 1) * (motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)) ^ 2)

/-- **Log-balancedness of Motzkin numbers plus their alternating sums.** Let $M_n$ denote the
$n$-th Motzkin number, let $T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$ be the alternating sum of
Motzkin numbers, and put $z_n = M_n + T_n$. Then the sequence $(z_n)_{n \ge 6}$ is log-balanced:
for every natural number $n \ge 7$,
$$z_n^2 \le z_{n-1} \, z_{n+1} \quad\text{and}\quad n \, z_{n-1} \, z_{n+1} \le (n+1) \, z_n^2.$$

The first inequality is log-convexity; for positive terms the second is log-concavity of
$z_n / n!$ with denominators cleared, the factorial using the original index $n$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 3. -/
public theorem_wanted motzkinNumber_add_motzkinAlternatingSum_logBalanced (n : ℕ) (hn : 7 ≤ n) :
    ((motzkinNumber n : ℤ) + motzkinAlternatingSum n) ^ 2 ≤
        ((motzkinNumber (n - 1) : ℤ) + motzkinAlternatingSum (n - 1)) *
          ((motzkinNumber (n + 1) : ℤ) + motzkinAlternatingSum (n + 1)) ∧
      n * (((motzkinNumber (n - 1) : ℤ) + motzkinAlternatingSum (n - 1)) *
          ((motzkinNumber (n + 1) : ℤ) + motzkinAlternatingSum (n + 1))) ≤
        (n + 1) * ((motzkinNumber n : ℤ) + motzkinAlternatingSum n) ^ 2

/-- **The alternating Fibonacci sums are eventually tempered.** Let $F_k$ denote the $k$-th
Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, and let $W_n = \sum_{k=0}^{n} (-1)^{n-k} F_k$.
For every natural number $n \ge 12$,
$$n W_n^2 \le (n+1) W_{n-1} W_{n+1} \quad\text{and}\quad n W_{n-1} W_{n+1} \le (n+1) W_n^2.$$

These are the conditions $\frac{n}{n+1} x_{n-1} \le x_n \le \frac{n+1}{n} x_{n-1}$ on the
quotients $x_n = W_{n+1}/W_n$, cleared of denominators (all terms are positive here), so the
sequence $(W_n)_{n \ge 11}$ is tempered, with the conditions imposed at every index $n \ge 12$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 4. -/
public theorem_wanted fibonacciAlternatingSum_tempered (n : ℕ) (hn : 12 ≤ n) :
    n * fibonacciAlternatingSum n ^ 2 ≤
        (n + 1) * (fibonacciAlternatingSum (n - 1) * fibonacciAlternatingSum (n + 1)) ∧
      n * (fibonacciAlternatingSum (n - 1) * fibonacciAlternatingSum (n + 1)) ≤
        (n + 1) * fibonacciAlternatingSum n ^ 2

end

end MetaMathlibExt
