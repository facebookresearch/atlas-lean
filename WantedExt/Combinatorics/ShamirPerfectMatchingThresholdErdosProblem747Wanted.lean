/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shamir's problem (Erdős Problem 747)

Erdős Problem 747 (Shamir): how large should `ℓ(n)` be such that, almost surely, a random
`3`-uniform hypergraph on `3n` vertices with `ℓ(n)` edges must contain `n` vertex-disjoint edges?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.ShamirPerfectMatchingThresholdErdosProblem747Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #747, https://www.erdosproblems.com/747 (status
SOLVED). UnsolvedMath record UM-30007009 (`EP-747`), dataset ulamai/UnsolvedMath v1.8.0.

The random hypergraph is uniform over the `ℓ`-element sets of triples of `Fin (3n)`, so the
probability is a ratio of counts. "Almost surely" is probability tending to `1`. The answer, a
threshold `∼ n log n`, is stated as two targets: Kahn's theorem (probability `→ 1` at `⌈(1 + ε) n
log n⌉` edges), and the threshold `ℓ_c(n)`, the least `ℓ` with probability at least `1/2` (Kahn's
definition), satisfies `ℓ_c(n) / (n log n) → 1` (natural logarithm; `n log n` and `(3n/3) log(3n)`
are asymptotic).
-/

open Filter Topology

open Classical in
/-- **Probability of a perfect matching in a random $3$-uniform hypergraph.** For natural numbers
$n$ and $\ell$, let $T$ be the set of $3$-element subsets of $\{0, 1, \dots, 3n - 1\}$. This is the
proportion of the $\ell$-element subsets $E \subseteq T$ that contain $n$ pairwise disjoint
triples, that is, the probability that the uniformly random $3$-uniform hypergraph on $3n$
vertices with $\ell$ edges has a perfect matching. When $\ell > \binom{3n}{3}$ there is no such
hypergraph and the value is $0$. -/
noncomputable def matchingProbability (n ℓ : ℕ) : ℝ :=
  (((Finset.univ.filter fun e : Finset (Fin (3 * n)) => e.card = 3).powersetCard ℓ).filter
      fun E => ∃ M : Finset (Finset (Fin (3 * n))), M ⊆ E ∧ M.card = n ∧
        (M : Set (Finset (Fin (3 * n)))).PairwiseDisjoint id).card /
    ((Finset.univ.filter fun e : Finset (Fin (3 * n)) => e.card = 3).powersetCard ℓ).card

/-- **Statement of the upper half of Shamir's problem.** The proposition that for every real
$\varepsilon > 0$, the probability that the uniformly random $3$-uniform hypergraph on $3n$
vertices with $\lceil (1 + \varepsilon) n \log n \rceil$ edges has a perfect matching ($n$
pairwise disjoint edges) tends to $1$ as $n \to \infty$, where $\log$ is the natural logarithm.

Erdős Problem 747 (Shamir's problem) asks for the number $\ell(n)$ of edges at which a perfect
matching becomes almost sure; this is the upper half of the answer $\ell(n) \sim n \log n$. -/
def matchingAboveThreshold : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => matchingProbability n ⌈(1 + ε) * n * Real.log n⌉₊) atTop (𝓝 1)

/-- **Threshold for a perfect matching in a random $3$-uniform hypergraph.** For a natural number
$n$, the threshold $\ell_c(n)$ is the least natural number $\ell$ such that the uniformly random
$3$-uniform hypergraph on $3n$ vertices with $\ell$ edges has a perfect matching ($n$ pairwise
disjoint edges) with probability at least $1/2$.

The set of such $\ell$ is nonempty: with all triples present the probability is $1$. -/
noncomputable def matchingThreshold (n : ℕ) : ℕ :=
  sInf {ℓ | 1 / 2 ≤ matchingProbability n ℓ}

/-- **Statement of Shamir's problem: the matching threshold is asymptotic to $n \log n$.** Let
$\ell_c(n)$ be the least number $\ell$ such that the uniformly random $3$-uniform hypergraph on
$3n$ vertices with $\ell$ edges has a perfect matching with probability at least $1/2$. The
proposition that $\ell_c(n) / (n \log n) \to 1$ as $n \to \infty$, where $\log$ is the natural
logarithm.

This is the answer to Erdős Problem 747 (Shamir's problem). -/
def matchingThresholdAsymptotic : Prop :=
  Tendsto (fun n : ℕ => (matchingThreshold n : ℝ) / (n * Real.log n)) atTop (𝓝 1)

/--
**Kahn's theorem on Shamir's problem, upper half.** For every real $\varepsilon > 0$, the
probability that the uniformly random $3$-uniform hypergraph on $3n$ vertices with
$\lceil (1 + \varepsilon) n \log n \rceil$ edges has a perfect matching ($n$ pairwise disjoint
edges) tends to $1$ as $n \to \infty$, where $\log$ is the natural logarithm.

Source: T. F. Bloom, Erdős Problems, Problem #747,
https://www.erdosproblems.com/747 (status SOLVED); resolution: J. Kahn, Asymptotics for Shamir's
problem, Adv. Math. 422 (2023), Paper 109019, Theorem 1 of arXiv:1909.06834 (abstract; Theorem 1.2
in the text): for fixed r ≥ 3, ε > 0 and M > (1 + ε)(n/r) log n, the random M-edge r-graph on [n]
has a perfect matching with probability → 1; Section 1: the threshold M_c, the least M for which the
probability of a perfect matching is at least 1/2, satisfies M_c ∼ (n/r) log n ('In this paper we
show that the asymptotics of the threshold are as expected'); erdosproblems.com/747: the threshold
is ∼ n log n, https://arxiv.org/abs/1909.06834.
-/
public theorem_wanted matchingAboveThreshold_holds : matchingAboveThreshold

/--
**Kahn's theorem: the threshold in Shamir's problem is asymptotic to $n \log n$.** Let $\ell_c(n)$
be the least number $\ell$ such that the uniformly random $3$-uniform hypergraph on $3n$ vertices
with $\ell$ edges has a perfect matching with probability at least $1/2$. Then
$\ell_c(n) / (n \log n) \to 1$ as $n \to \infty$, where $\log$ is the natural logarithm.

Source:
T. F. Bloom, Erdős Problems, Problem #747, https://www.erdosproblems.com/747 (status SOLVED);
resolution: J. Kahn, Asymptotics for Shamir's problem, Adv. Math. 422 (2023), Paper 109019, Theorem
1 of arXiv:1909.06834 (abstract; Theorem 1.2 in the text): for fixed r ≥ 3, ε > 0 and M > (1 +
ε)(n/r) log n, the random M-edge r-graph on [n] has a perfect matching with probability → 1; Section
1: the threshold M_c, the least M for which the probability of a perfect matching is at least 1/2,
satisfies M_c ∼ (n/r) log n ('In this paper we show that the asymptotics of the threshold are as
expected'); erdosproblems.com/747: the threshold is ∼ n log n, https://arxiv.org/abs/1909.06834.
-/
public theorem_wanted matchingThresholdAsymptotic_holds : matchingThresholdAsymptotic

end MathlibExt.Combinatorics.ShamirPerfectMatchingThresholdErdosProblem747Wanted
