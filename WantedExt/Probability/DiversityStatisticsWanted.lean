/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integer sequences for diversity statistics

Statements from Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", *Journal
of Integer Sequences* 29 (2026), Article 26.1.5
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Rosenberg/rosen5.html>).

A sample of size `N` is recorded by its list of type
counts. The Gini-Simpson index is `1 - ∑ (a / N)^2`, so
its number of distinct values `γ(N)` equals the number
of distinct values of `∑ a^2`; the Shannon index is
`-∑ (a / N) log (a / N)` and `σ(N)` counts its distinct
values. The bounds on `γ` were verified by partition
enumeration for `N ≤ 30`.

Not stated (see the source audit table): Propositions
1 and 2 (quoted bounds of Rosenberg relating the
maximal cell probability to `∑ p_i^2` and to the
Shannon index) and Theorem 3 (whose bounding
functions `M_min`, `M_max`, `S_min`, `S_max` are
defined in missing equations).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Topology.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Probability.DiversityStatisticsWanted

/-- **Number of values of the Gini–Simpson index.** For a natural number $N$, $\gamma(N)$ is the
number of distinct values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$
of natural numbers with $a_1 + \dots + a_k = N$.

For $N \ge 1$, the Gini–Simpson index of a sample of size $N$ with type counts $a_1, \dots, a_k$ is
$1 - \sum_i (a_i / N)^2$, so $\gamma(N)$ is the number of possible values of the Gini–Simpson index
across all samples of size $N$. -/
noncomputable def giniSimpsonCount (N : ℕ) : ℕ :=
  Set.ncard {s : ℕ | ∃ l : List ℕ, l.sum = N ∧
    (l.map (fun a => a ^ 2)).sum = s}

/-- **Number of values of the Shannon index.** For a natural number $N$, $\sigma(N)$ is the number
of distinct real numbers $-\sum_{i=1}^{k} (a_i / N) \log (a_i / N)$ over all finite sequences $(a_1,
\dots, a_k)$ of natural numbers with $a_1 + \dots + a_k = N$, where a term with $a_i = 0$ counts as
$0$ (the convention $0 \log 0 = 0$).

For $N \ge 1$, this is the number of possible values of the Shannon index across all samples of size
$N$. -/
noncomputable def shannonCount (N : ℕ) : ℕ :=
  Set.ncard {v : ℝ | ∃ l : List ℕ, l.sum = N ∧
    v = -(l.map (fun a => ((a : ℝ) / N) * Real.log ((a : ℝ) / N))).sum}

/-- **Upper bound on the number of Gini–Simpson values.** Let $\gamma(N)$ be the number of distinct
values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$ of natural numbers
with $a_1 + \dots + a_k = N$ (for $N \ge 1$, the number of possible values of the Gini–Simpson index
across samples of size $N$). Then for every natural number $N$,
$$\gamma(N) \le \tfrac{1}{2} N^2 - \tfrac{1}{2} N + 1.$$

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 4. -/
theorem_wanted giniSimpsonCount_le (N : ℕ) :
    (giniSimpsonCount N : ℚ) ≤ (1 / 2) * N ^ 2 - (1 / 2) * N + 1

/-- **Triangular-number lower bound on the number of Gini–Simpson values.** Let $\gamma(N)$ be the
number of distinct values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$
of natural numbers with $a_1 + \dots + a_k = N$ (for $N \ge 1$, the number of possible values of the
Gini–Simpson index across samples of size $N$). Let $m$ and $r$ be natural numbers with $r \le m$,
and let $N = \binom{m+1}{2} + r$. Then
$$\tfrac{1}{3} m (m^2 + 3r - 1) + 1 \le \gamma(N).$$

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 5. -/
theorem_wanted giniSimpsonCount_ge_triangular (N m r : ℕ)
    (hN : N = (m + 1) * m / 2 + r) (hr : r ≤ m) :
    (1 / 3) * (m : ℚ) * ((m : ℚ) ^ 2 + 3 * r - 1) + 1 ≤
      (giniSimpsonCount N : ℚ)

/-- **Quadratic lower bound on the number of Gini–Simpson values.** Let $\gamma(N)$ be the number of
distinct values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$ of natural
numbers with $a_1 + \dots + a_k = N$ (for $N \ge 1$, the number of possible values of the
Gini–Simpson index across samples of size $N$). Then for every natural number $N$,
$$\tfrac{1}{2} \left( \lfloor N^2 / 5 \rfloor - N \right) \le \gamma(N).$$

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 6. -/
theorem_wanted giniSimpsonCount_ge (N : ℕ) :
    (((N ^ 2 / 5 : ℕ) : ℚ) - N) / 2 ≤ (giniSimpsonCount N : ℚ)

/-- **Asymptotics of the number of Gini–Simpson values.** Let $\gamma(N)$ be the number of distinct
values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$ of natural numbers
with $a_1 + \dots + a_k = N$ (for $N \ge 1$, the number of possible values of the Gini–Simpson index
across samples of size $N$). Then $\gamma(N) / N^2 \to 1/2$ as $N \to \infty$, that is, $\gamma(N)
\sim \tfrac{1}{2} N^2$.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 7. -/
theorem_wanted giniSimpsonCount_asymp :
    Filter.Tendsto
      (fun N : ℕ => (giniSimpsonCount N : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (1 / 2))

/-- **Upper bound on the number of Shannon values.** Let $\sigma(N)$ be the number of distinct real
numbers $-\sum_{i=1}^{k} (a_i / N) \log (a_i / N)$ over all finite sequences $(a_1, \dots, a_k)$ of
natural numbers with $a_1 + \dots + a_k = N$, where a term with $a_i = 0$ counts as $0$ (for $N \ge
1$, the number of possible values of the Shannon index across samples of size $N$). Then for every
natural number $N \ge 1$,
$$\sigma(N) \le \exp\left(\pi \sqrt{2/3} \sqrt{N}\right).$$

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 8. -/
theorem_wanted shannonCount_le (N : ℕ) (hN : 1 ≤ N) :
    (shannonCount N : ℝ) ≤
      Real.exp (Real.pi * Real.sqrt (2 / 3) * Real.sqrt N)

/-- **The number of Shannon values grows faster than every polynomial.** Let $\sigma(N)$ be the
number of distinct real numbers $-\sum_{i=1}^{k} (a_i / N) \log (a_i / N)$ over all finite sequences
$(a_1, \dots, a_k)$ of natural numbers with $a_1 + \dots + a_k = N$, where a term with $a_i = 0$
counts as $0$ (for $N \ge 1$, the number of possible values of the Shannon index across samples of
size $N$). Then for every nonzero polynomial $q$ with real coefficients, $\sigma(N) / |q(N)| \to
\infty$ as $N \to \infty$.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Theorem 9. -/
theorem_wanted shannonCount_superpolynomial
    (q : Polynomial ℝ) (hq : q ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => (shannonCount N : ℝ) / |q.eval (N : ℝ)|)
      Filter.atTop Filter.atTop

end MathlibExt.Probability.DiversityStatisticsWanted
