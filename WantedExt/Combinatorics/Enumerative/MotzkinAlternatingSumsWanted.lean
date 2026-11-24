/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.FibonacciAlternatingSums
public import MathlibExt.Combinatorics.Enumerative.MotzkinAlternatingSums
public import MathlibExt.Combinatorics.Enumerative.RiordanNumberEvenLogConvex

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
