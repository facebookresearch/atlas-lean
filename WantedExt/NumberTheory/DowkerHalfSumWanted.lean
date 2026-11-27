/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.WatsonAlternatingBounds
public import MathlibExt.NumberTheory.WatsonCoshIntegral
public import MathlibExt.NumberTheory.WatsonCotangentDerivatives
public import MathlibExt.NumberTheory.DowkerHalfSumWatsonCosSumSixthLimits

namespace MetaMathlibExt

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators Topology

/--
**Almost-asymptotic expansion of Watson's cosine sum.** Let $n \ge 2$, $N \ge 2$ and $\nu$ be
natural numbers with $1 \le \nu \le n - 1$, and let
$$
C_n(\nu) = \sum_{l=1}^{n-1} \frac{\cos(2 \pi \nu l / n)}{\sin(\pi l / n)}.
$$
For $r \ge 1$ write
$$
T_r(n, \nu) = \frac{(1 - 2^{1-2r}) \, \pi^{2r-1} B_{2r} \, \cot^{(2r-1)}(\pi \nu / n)}
{(2r)! \, n^{2r-1}},
$$
where $B_{2r}$ is the $2r$-th Bernoulli number and $\cot^{(2r-1)}$ is the $(2r-1)$-st derivative
of the cotangent. Then there is a real number $\lambda$ with $0 < \lambda < 1$ such that
$$
C_n(\nu) = -\frac{2n}{\pi} \log\left(2 \sin\frac{\pi \nu}{n}\right) +
2 \sum_{r=1}^{N-1} T_r(n, \nu) + 2 \lambda \, T_N(n, \nu).
$$

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
-/
public theorem_wanted watson_cos_sum_almost_asymptotic
    (n ν N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) (hνpos : 1 ≤ ν)
    (hνmax : ν ≤ n - 1) :
    ∃ remainder : ℝ, 0 < remainder ∧ remainder < 1 ∧
      watsonCosSum n ν =
        -(2 * (n : ℝ) / Real.pi) *
            Real.log (2 * Real.sin (Real.pi * (ν : ℝ) / (n : ℝ))) +
          2 * (∑ r ∈ Finset.Icc 1 (N - 1), watsonExpansionTerm r n ν) +
          2 * remainder * watsonExpansionTerm N n ν

/--
**Complete asymptotic expansion of Watson's alternating cosecant sum.** For natural numbers $N$
and $n$ let $C_n = \sum_{l=1}^{n-1} (-1)^{l+1} / \sin(\pi l / n)$ and
$$
M_N(n) = \frac{2 n \log 2}{\pi} + 2 \sum_{r=1}^{N-1}
\frac{(-1)^{r+1} (2^{2r-1} - 1)(2^{2r} - 1) \pi^{2r-1} B_{2r}^2}{r \, (2r)! \, n^{2r-1}},
$$
where $B_{2r}$ is the $2r$-th Bernoulli number. For every $N \ge 2$ there is a real constant
$K \ge 0$ such that for every even $n \ge 2$,
$$
|C_n - M_N(n)| \le \frac{K}{n^{2N-1}}.
$$
In other words, $C_n = M_N(n) + O(n^{1-2N})$ as $n \to \infty$ through even values.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2.
-/
public theorem_wanted watson_alternating_complete_asymptotic (N : ℕ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, Even n → 2 ≤ n →
      |watsonAlternatingCosecantSum n - watsonAlternatingMain N n| ≤
        K / (n : ℝ) ^ (2 * N - 1)

/--
**Two-sided bounds for Watson's alternating cosecant sum.** For every even natural number
$n \ge 2$, the alternating cosecant sum $C_n = \sum_{l=1}^{n-1} (-1)^{l+1} / \sin(\pi l / n)$
satisfies the strict inequalities
$$
\frac{2 n \log 2}{\pi} + \frac{\pi}{12 n} - \frac{7 \pi^3}{1440 n^3} < C_n <
\frac{2 n \log 2}{\pi} + \frac{\pi}{12 n}.
$$
The lower bound consists of the first three terms of the asymptotic expansion of $C_n$ and the
upper bound of the first two.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 6 and Corollary 3.
-/
public theorem_wanted watson_alternating_sharp_bounds
    (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    2 * (n : ℝ) * Real.log 2 / Real.pi + Real.pi / (12 * (n : ℝ)) -
          7 * Real.pi ^ 3 / (1440 * (n : ℝ) ^ 3) <
        watsonAlternatingCosecantSum n ∧
      watsonAlternatingCosecantSum n <
        2 * (n : ℝ) * Real.log 2 / Real.pi + Real.pi / (12 * (n : ℝ))

end

end MetaMathlibExt
