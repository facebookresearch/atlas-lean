/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Enumerative.GeneralizedLeonardoLogBehavior
public import WantedExt.NumberTheory.GenLeonardoWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Log-balancedness of the reciprocals of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer and let $L_{k,n}$ be the generalized Leonardo numbers. Then the sequence
$(1/L_{k,n})_{n \ge 3}$ is log-balanced (Došlić): for every integer $n \ge 4$,
$$\left(\frac{1}{L_{k,n}}\right)^2 \le \frac{1}{L_{k,n-1}} \cdot \frac{1}{L_{k,n+1}}$$
and
$$\frac{1}{L_{k,n-1} \, (n-1)!} \cdot \frac{1}{L_{k,n+1} \, (n+1)!} \le
\left(\frac{1}{L_{k,n} \, n!}\right)^2.$$

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 1
(`integers-2024-A82-thm-1`). -/
public theorem_wanted inv_genLeonardo_logBalanced (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 4 ≤ n) :
    (1 / (genLeonardo k n : ℝ)) ^ 2 ≤
        (1 / (genLeonardo k (n - 1) : ℝ)) * (1 / (genLeonardo k (n + 1) : ℝ)) ∧
      (1 / (genLeonardo k (n - 1) : ℝ) / (n - 1).factorial) *
          (1 / (genLeonardo k (n + 1) : ℝ) / (n + 1).factorial) ≤
        (1 / (genLeonardo k n : ℝ) / n.factorial) ^ 2

/-- **Log-convexity of the n-th roots of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer and let $L_{k,n}$ be the generalized Leonardo numbers. Then the sequence
$(L_{k,n}^{1/n})_{n \ge 9}$ is log-convex:
$(L_{k,n}^{1/n})^2 \le L_{k,n-1}^{1/(n-1)} L_{k,n+1}^{1/(n+1)}$ for every integer $n \ge 10$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 3
(`integers-2024-A82-thm-3`). -/
public theorem_wanted genLeonardo_rpow_inv_logConvex (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 10 ≤ n) :
    ((genLeonardo k n : ℝ) ^ ((1 : ℝ) / n)) ^ 2 ≤
      (genLeonardo k (n - 1) : ℝ) ^ ((1 : ℝ) / (n - 1 : ℕ)) *
        (genLeonardo k (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1 : ℕ))

/-- **Log-balancedness of the n-th roots of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer, let $L_{k,n}$ be the generalized Leonardo numbers, and let $n_k$ be an integer with
$n_k \ge 9$ and $n_k \ge (1 + \sqrt{64k - 7})/4$. Then for every integer $n \ge n_k + 1$,
$$\left(L_{k,n}^{1/n}\right)^2 \le L_{k,n-1}^{1/(n-1)} L_{k,n+1}^{1/(n+1)}$$
and
$$\frac{L_{k,n-1}^{1/(n-1)}}{(n-1)!} \cdot \frac{L_{k,n+1}^{1/(n+1)}}{(n+1)!} \le
\left(\frac{L_{k,n}^{1/n}}{n!}\right)^2;$$
that is, the sequence $(L_{k,n}^{1/n})_{n \ge n_k}$ is log-balanced (Došlić): it is log-convex
and its quotient by $n!$ is log-concave.

The paper asserts only that some $n_k \ge \max\{9, (1 + \sqrt{64k - 7})/4\}$ with this property
exists; the statement above gives the threshold its proof establishes (log-concavity of
$L_{k,n}^{1/n}/n!$ once $n \ge (1 + \sqrt{64k - 7})/4$, log-convexity of $L_{k,n}^{1/n}$ from
$n = 9$ on).

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 4
(`integers-2024-A82-thm-4`). -/
public theorem_wanted genLeonardo_rpow_inv_logBalanced (k : ℕ) (hk : 1 ≤ k) (nk : ℕ)
    (h9 : 9 ≤ nk) (hsqrt : (1 + Real.sqrt (64 * k - 7)) / 4 ≤ nk) :
    ∀ n : ℕ, nk + 1 ≤ n →
      ((genLeonardo k n : ℝ) ^ ((1 : ℝ) / n)) ^ 2 ≤
          (genLeonardo k (n - 1) : ℝ) ^ ((1 : ℝ) / (n - 1 : ℕ)) *
            (genLeonardo k (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1 : ℕ)) ∧
        (genLeonardo k (n - 1) : ℝ) ^ ((1 : ℝ) / (n - 1 : ℕ)) / (n - 1).factorial *
            ((genLeonardo k (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1 : ℕ)) / (n + 1).factorial) ≤
          ((genLeonardo k n : ℝ) ^ ((1 : ℝ) / n) / n.factorial) ^ 2

/-- **Log-convexity of the self-powers of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer and let $L_{k,n}$ be the generalized Leonardo numbers. Then the sequence
$(L_{k,n}^n)_{n \ge 3}$ is log-convex: $L_{k,n}^{2n} \le L_{k,n-1}^{n-1} L_{k,n+1}^{n+1}$ for
every integer $n \ge 4$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 5
(`integers-2024-A82-thm-5`). -/
public theorem_wanted genLeonardo_pow_self_logConvex (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 4 ≤ n) :
    genLeonardo k n ^ (2 * n) ≤ genLeonardo k (n - 1) ^ (n - 1) * genLeonardo k (n + 1) ^ (n + 1)

end

end MetaMathlibExt
