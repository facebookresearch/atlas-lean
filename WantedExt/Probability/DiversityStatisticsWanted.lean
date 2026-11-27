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

Propositions 1 and 2 (bounds quoted from Rosenberg and
from Aw and Rosenberg) and Theorem 3 use the paper's
bounding functions `M_min`, `M_max`, `S_min`, `S_max`
(Eqs. (1)-(4) of Section 2), here `diversityMmin`,
`diversityMmax`, `diversitySmin`, `diversitySmax`.
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
public import MathlibExt.Probability.DiversityStatistics
public import MathlibExt.Probability.GiniSimpsonAsymptotics
public import MathlibExt.Probability.GiniSimpsonTriangular

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Probability.DiversityStatisticsWanted

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

/-- **Proposition 1** (quoted from Rosenberg, Thm. 2.7): for a
probability vector `p` on `I ≥ 2` cells with at least two
nonzero entries, `J = ∑ p_i^2` and `M = max p_i`,
`M_min(J) ≤ M ≤ M_max(J)`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Proposition 1 (`jis-2026-26.1.5-prop-1`). `M` is any
greatest value of `p`. -/
theorem_wanted diversityMmin_le_max_le_diversityMmax {I : ℕ} (hI : 2 ≤ I) (p : Fin I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hp2 : ∃ i j, i ≠ j ∧ p i ≠ 0 ∧ p j ≠ 0)
    (M : ℝ) (hM : IsGreatest (Set.range p) M) :
    diversityMmin (∑ i, p i ^ 2) ≤ M ∧ M ≤ diversityMmax I (∑ i, p i ^ 2)

/-- **Proposition 2** (quoted from Aw and Rosenberg,
Cor. 3.16): for a probability vector `p` on `I ≥ 2` cells
with at least two nonzero entries, `M = max p_i` and Shannon
index `S = -∑ p_i log p_i`, `S_min(M) ≤ S ≤ S_max(M)`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Proposition 2 (`jis-2026-26.1.5-prop-2`). `0 log 0 = 0`
matches `Real.log 0 = 0`. -/
theorem_wanted diversitySmin_le_shannon_le_diversitySmax {I : ℕ} (hI : 2 ≤ I) (p : Fin I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hp2 : ∃ i j, i ≠ j ∧ p i ≠ 0 ∧ p j ≠ 0)
    (M : ℝ) (hM : IsGreatest (Set.range p) M) :
    diversitySmin M ≤ -∑ i, p i * Real.log (p i) ∧
      -∑ i, p i * Real.log (p i) ≤ diversitySmax I M

/-- **Theorem 3**: for a probability vector `p` on `I ≥ 2`
cells with at least two nonzero entries and Gini-Simpson index
`H = 1 - ∑ p_i^2`, the Shannon index satisfies
`S_min(M_max(1 - H)) ≤ S ≤ S_max(M_min(1 - H))`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Theorem 3 (`jis-2026-26.1.5-thm-3`). The paper's
hypothesis `0 < H ≤ 1 - 1/I` holds for every such `p` and is
not repeated; `1 - H` is written as `∑ p_i^2`. -/
theorem_wanted diversitySmin_diversityMmax_le_shannon_le {I : ℕ} (hI : 2 ≤ I) (p : Fin I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hp2 : ∃ i j, i ≠ j ∧ p i ≠ 0 ∧ p j ≠ 0) :
    diversitySmin (diversityMmax I (∑ i, p i ^ 2)) ≤ -∑ i, p i * Real.log (p i) ∧
      -∑ i, p i * Real.log (p i) ≤ diversitySmax I (diversityMmin (∑ i, p i ^ 2))

end MathlibExt.Probability.DiversityStatisticsWanted
