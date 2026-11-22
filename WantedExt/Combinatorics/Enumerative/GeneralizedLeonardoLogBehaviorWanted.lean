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
public import WantedExt.NumberTheory.GenLeonardoWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Log-concavity propagates along a linear recurrence.** Let $k \ge 2$ be an integer, let
$c_1, \dots, c_k$ be real numbers with $c_j \ge 0$ for $2 \le j \le k$, and let
$(z_n)_{n \ge 0}$ be a sequence of positive real numbers with
$$z_n = c_1 z_{n-1} - \sum_{j=2}^{k} c_j z_{n-j} \quad (n \ge k).$$
If $z_{i-1} z_{i+1} \le z_i^2$ for $1 \le i < k$, then $z_{n-1} z_{n+1} \le z_n^2$ for every
$n \ge 1$; that is, the whole sequence is log-concave.

The paper assumes that the block $z_0, \dots, z_{k+1}$ is log-concave, which adds the
inequality for $i = k$, and that $c_1 > 0$. Both follow from the other hypotheses: the
recurrence at $n = k + 1$ propagates the inequality for $i = k$ from those for $i < k$, and
the recurrence at $n = k$ forces $c_1 > 0$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 1
(quoted from the paper's reference [17]) (`integers-2024-A82-lem-1`). -/
public theorem_wanted logConcave_of_linearRecurrence_of_initial_logConcave
    (k : ℕ) (hk : 2 ≤ k) (c : ℕ → ℝ) (hc : ∀ j, 2 ≤ j → j ≤ k → 0 ≤ c j)
    (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, k ≤ n →
      z n = c 1 * z (n - 1) - ∑ j ∈ Finset.Icc 2 k, c j * z (n - j))
    (hinit : ∀ i, 1 ≤ i → i < k → z (i - 1) * z (i + 1) ≤ z i ^ 2) :
    ∀ n, 1 ≤ n → z (n - 1) * z (n + 1) ≤ z n ^ 2

/-- **Log-convexity propagates along a linear recurrence.** Let $k \ge 2$ be an integer, let
$c_1, \dots, c_k$ be real numbers with $c_j \ge 0$ for $2 \le j \le k$, and let
$(z_n)_{n \ge 0}$ be a sequence of positive real numbers with
$$z_n = c_1 z_{n-1} - \sum_{j=2}^{k} c_j z_{n-j} \quad (n \ge k).$$
If $z_i^2 \le z_{i-1} z_{i+1}$ for $1 \le i < k$, then $z_n^2 \le z_{n-1} z_{n+1}$ for every
$n \ge 1$; that is, the whole sequence is log-convex.

The paper assumes that the block $z_0, \dots, z_{k+1}$ is log-convex, which adds the
inequality for $i = k$, and that $c_1 > 0$. Both follow from the other hypotheses: the
recurrence propagates the inequality for $i = k$, and the recurrence at $n = k$ forces
$c_1 > 0$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 1,
log-convex reading (quoted from the paper's reference [17])
(`integers-2024-A82-lem-1`). -/
public theorem_wanted logConvex_of_linearRecurrence_of_initial_logConvex
    (k : ℕ) (hk : 2 ≤ k) (c : ℕ → ℝ) (hc : ∀ j, 2 ≤ j → j ≤ k → 0 ≤ c j)
    (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, k ≤ n →
      z n = c 1 * z (n - 1) - ∑ j ∈ Finset.Icc 2 k, c j * z (n - j))
    (hinit : ∀ i, 1 ≤ i → i < k → z i ^ 2 ≤ z (i - 1) * z (i + 1)) :
    ∀ n, 1 ≤ n → z n ^ 2 ≤ z (n - 1) * z (n + 1)

/-- **Log-balancedness of reciprocals along a three-term recurrence.** Let $c_1$ and $c_2$ be
real numbers with $c_2 \ge 0$, and let $(z_n)_{n \ge 0}$ be a sequence of positive real numbers
with $z_{n+1} = c_1 z_n - c_2 z_{n-2}$ for every $n \ge 2$. Write $w_n = 1/z_n$ and
$x_n = z_{n+1}/z_n$, and let $n_0 \ge 0$ be an integer. Suppose that for $n = n_0 + 1$ and
$n = n_0 + 2$
$$w_n^2 \le w_{n-1} w_{n+1} \quad \text{and} \quad
\frac{w_{n-1}}{(n-1)!} \cdot \frac{w_{n+1}}{(n+1)!} \le \left(\frac{w_n}{n!}\right)^2,$$
and that $c_1 x_n x_{n+1} \ge 3 c_2$ for every $n \ge n_0$. Then both inequalities hold for
every $n \ge n_0 + 1$; that is, the sequence $(1/z_n)_{n \ge n_0}$ is log-balanced (Došlić).

The paper also assumes $c_1 > 0$; this follows from positivity, the recurrence and $c_2 \ge 0$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 2
(`integers-2024-A82-lem-2`). -/
public theorem_wanted inv_logBalanced_of_recurrence_of_initial (c₁ c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, 2 ≤ n → z (n + 1) = c₁ * z n - c₂ * z (n - 2)) (n₀ : ℕ)
    (hinit : ∀ n, n₀ + 1 ≤ n → n ≤ n₀ + 2 →
      (1 / z n) ^ 2 ≤ (1 / z (n - 1)) * (1 / z (n + 1)) ∧
        (1 / z (n - 1) / (n - 1).factorial) * (1 / z (n + 1) / (n + 1).factorial) ≤
          (1 / z n / n.factorial) ^ 2)
    (hx : ∀ n, n₀ ≤ n → 3 * c₂ ≤ c₁ * (z (n + 1) / z n) * (z (n + 2) / z (n + 1))) :
    ∀ n, n₀ + 1 ≤ n →
      (1 / z n) ^ 2 ≤ (1 / z (n - 1)) * (1 / z (n + 1)) ∧
        (1 / z (n - 1) / (n - 1).factorial) * (1 / z (n + 1) / (n + 1).factorial) ≤
          (1 / z n / n.factorial) ^ 2

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

/-- **Log-concavity of partial sums of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer, let $L_{k,n}$ be the generalized Leonardo numbers, and let
$R_n = \sum_{i=0}^{n} L_{k,i}$. Then $R_{n-1} R_{n+1} \le R_n^2$ for every integer $n \ge 2$.

The inequality fails at $n = 1$: there $R_0 = 1$, $R_1 = 2$ and $R_2 = k + 4$, so
$R_1^2 - R_0 R_2 = -k < 0$. The paper states it for every $n \ge 1$, although its identity
$R_n^2 - R_{n-1} R_{n+1} = (k+1)^2 (F_n + (-1)^n) + k(k+1)(n F_n - 2 F_{n+1}) + k^2$, with
$F_n$ the Fibonacci numbers, gives the same value $-k$ at $n = 1$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 2
(`integers-2024-A82-thm-2`). -/
public theorem_wanted genLeonardo_partialSum_logConcave (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 2 ≤ n) :
    (∑ i ∈ Finset.range n, genLeonardo k i) * (∑ i ∈ Finset.range (n + 2), genLeonardo k i) ≤
      (∑ i ∈ Finset.range (n + 1), genLeonardo k i) ^ 2

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
