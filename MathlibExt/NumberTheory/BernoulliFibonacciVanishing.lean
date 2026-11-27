/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.BernoulliFibonacciExpansion

/-!
# A vanishing Bernoulli–Fibonacci double sum

We prove that the Bernoulli–Fibonacci double sum with weight `(-fibBeta) ^ (m - n)` vanishes
for every positive exponent `m`, by specializing the expansion of `(x + fibBeta) ^ m`.
-/

public section

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

/-- **A vanishing double sum of Bernoulli and Fibonacci numbers.** Let $\beta = (1 - \sqrt{5})/2$,
let $F_n$ be the Fibonacci numbers, and let $B_k$ be the Bernoulli numbers, with
$B_1 = -\tfrac{1}{2}$. For every natural number $m \ge 1$,
$$\sum_{n=0}^{m} \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} \binom{m}{n} B_k
\frac{F_{n-k+1}}{n-k+1} (-\beta)^{m-n} = 0.$$

This is the case $x = -\beta$ of Theorem 1, the expansion of $(x + \beta)^m$. The paper prints
the factor $\beta^{-n}$ in place of $(-\beta)^{m-n}$, which makes the sum equal to $2^m$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 2. -/
theorem sum_bernoulli_fib_neg_fibBeta (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (-fibBeta) ^ (m - n) = 0 := by
  simpa [zero_pow (Nat.ne_of_gt hm)] using
    (descFactorial_mul_add_fibBeta_pow m 0 (Nat.zero_le m) (-fibBeta)).symm

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
