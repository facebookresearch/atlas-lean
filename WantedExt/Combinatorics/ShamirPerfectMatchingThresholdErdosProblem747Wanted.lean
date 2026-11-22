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
/-- The probability that the uniformly random `3`-uniform hypergraph on `3n` vertices with `ℓ`
edges (a uniformly random `ℓ`-element set of triples of `Fin (3n)`) contains `n` pairwise
vertex-disjoint edges. -/
noncomputable def matchingProbability (n ℓ : ℕ) : ℝ :=
  (((Finset.univ.filter fun e : Finset (Fin (3 * n)) => e.card = 3).powersetCard ℓ).filter
      fun E => ∃ M : Finset (Finset (Fin (3 * n))), M ⊆ E ∧ M.card = n ∧
        (M : Set (Finset (Fin (3 * n)))).PairwiseDisjoint id).card /
    ((Finset.univ.filter fun e : Finset (Fin (3 * n)) => e.card = 3).powersetCard ℓ).card

/-- Erdős Problem 747 (Shamir's problem), upper half of the threshold `ℓ(n) ∼ n log n`: with
`ℓ(n) = ⌈(1 + ε) n log n⌉` edges the random hypergraph has `n` disjoint edges with probability
tending to `1`. -/
def matchingAboveThreshold : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => matchingProbability n ⌈(1 + ε) * n * Real.log n⌉₊) atTop (𝓝 1)

/-- The threshold `ℓ_c(n)`: the least `ℓ` such that the random `3`-uniform hypergraph on `3n`
vertices with `ℓ` edges has `n` disjoint edges with probability at least `1 / 2` (the set is
nonempty: with all triples present the probability is `1`). -/
noncomputable def matchingThreshold (n : ℕ) : ℕ :=
  sInf {ℓ | 1 / 2 ≤ matchingProbability n ℓ}

/-- Erdős Problem 747 (Shamir's problem), the answer: the threshold is asymptotic to `n log n`,
i.e. `ℓ_c(n) / (n log n) → 1`. -/
def matchingThresholdAsymptotic : Prop :=
  Tendsto (fun n : ℕ => (matchingThreshold n : ℝ) / (n * Real.log n)) atTop (𝓝 1)

/--
Resolved true: Kahn proved that with `M > (1 + ε)(N / r) log N` edges the random `r`-graph on `N`
vertices has a perfect matching with probability tending to `1` (here `r = 3`, `N = 3n`), completing
the threshold `∼ n log n` (Johansson, Kahn and Vu had `≍ n log n`); erdosproblems.com/747 lists the
problem as solved. Source: T. F. Bloom, Erdős Problems, Problem #747,
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
Resolved true: Kahn proved that the threshold for a perfect matching in the random `r`-uniform
hypergraph on `N` vertices (the least number of edges at which a perfect matching appears with
probability at least `1/2`) is `∼ (N / r) log N`; with `r = 3` and `N = 3n` this is `∼ n log n`, the
answer recorded on erdosproblems.com/747 (Johansson, Kahn and Vu had the order `n log n`). Source:
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
