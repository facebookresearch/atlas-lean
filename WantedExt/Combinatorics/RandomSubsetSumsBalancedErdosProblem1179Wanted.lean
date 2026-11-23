/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equidistribution of subset sums of random subsets of abelian groups (Erdős Problem 1179)

Erdős Problem 1179: for `0 < ε < 1` let `g_ε(N)` be the least `k` such that for an abelian group `G`
of size `N` and a uniformly random `k`-subset `A`, with probability `→ 1` as `N → ∞` every `g ∈ G`
has `|F_A(g) - 2^k/N| ≤ ε 2^k/N`, where `F_A(g)` counts subsets of `A` with sum `g`. Is `g_ε(N) = (1
+ o_ε(1)) log₂ N`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace MathlibExt.Combinatorics.RandomSubsetSumsBalancedErdosProblem1179Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1179, https://www.erdosproblems.com/1179 (status
PROVED). UnsolvedMath record UM-30007220 (`EP-1179`), dataset ulamai/UnsolvedMath v1.8.0.

The target states `g_ε(N) = (1 + o(1)) log₂ N` as two bounds. Upper: sizes `k(N) = (1 + o(1)) log₂
N` for which the success probability tends to `1` along every sequence of finite abelian groups with
`|G| → ∞` (equivalently, uniformly over the groups of order `N`). Lower: every `ε`-balanced subset
`A` of a group of order `N` has `2^{|A|} ≥ N`, so no size below `log₂ N` succeeds (the source calls
this bound trivial: balance with `ε < 1` makes every `g` a subset sum). Compared with the
formal-conjectures statement `ErdosProblems/1179.lean` (the conjunction of `erdos_1179` and
`erdos_1179.variants.lower_bound`; no code imported).
-/

open Filter Finset

open scoped Classical in
/-- **Number of subsets with a given sum.** For a finite subset $A$ of an abelian group $G$ and an
element $g \in G$, $F_A(g)$ is the number of subsets $S \subseteq A$, the empty set included, whose
elements sum to $g$, that is, with $\sum_{x \in S} x = g$. -/
noncomputable def subsetSumCount {G : Type*} [AddCommGroup G] (A : Finset G) (g : G) : ℕ :=
  (A.powerset.filter fun S => ∑ x ∈ S, x = g).card

/-- **$\varepsilon$-balanced subsets of a finite abelian group.** Let $G$ be a finite abelian group
with $N = |G|$ elements and let $\varepsilon$ be a real number. A subset $A \subseteq G$ is
$\varepsilon$-balanced when, for every $g \in G$, the number $F_A(g)$ of subsets of $A$ whose
elements sum to $g$ satisfies
$\left| F_A(g) - 2^{|A|}/N \right| \le \varepsilon \cdot 2^{|A|}/N$. -/
def IsBalanced {G : Type*} [AddCommGroup G] [Fintype G] (ε : ℝ) (A : Finset G) : Prop :=
  ∀ g : G, |(subsetSumCount A g : ℝ) - 2 ^ A.card / Fintype.card G| ≤
    ε * (2 ^ A.card / Fintype.card G)

open scoped Classical in
/-- **Probability that a random subset is balanced.** For a finite abelian group $G$, a real
number $\varepsilon$ and a natural number $k$, this is the number of $\varepsilon$-balanced
$k$-element subsets of $G$ divided by the number of all $k$-element subsets of $G$, that is, the
probability that a uniformly random $k$-element subset of $G$ is $\varepsilon$-balanced. When
$k > |G|$ there are no $k$-element subsets and the value is $0$. -/
noncomputable def balancedProbability (G : Type*) [AddCommGroup G] [Fintype G] (ε : ℝ) (k : ℕ) :
    ℝ :=
  (((univ : Finset G).powersetCard k).filter (IsBalanced ε)).card /
    ((univ : Finset G).powersetCard k).card

/-- **Erdős Problem 1179 (balanced subset sums of random subsets).** The statement of Erdős
Problem 1179 is the proposition that, for every real $\varepsilon$ with $0 < \varepsilon < 1$, the
following two bounds hold. Upper bound: there is a function $k : \mathbb{N} \to \mathbb{N}$ with
$k(N) / \log_2 N \to 1$ as $N \to \infty$ such that, for every sequence $(G_i)_{i \in \mathbb{N}}$
of finite abelian groups with $|G_i| \to \infty$, the probability that a uniformly random
$k(|G_i|)$-element subset of $G_i$ is $\varepsilon$-balanced tends to $1$ as $i \to \infty$. Lower
bound: for every finite abelian group $G$, every $\varepsilon$-balanced subset $A \subseteq G$
satisfies $|G| \le 2^{|A|}$. -/
def balancedSubsetSumsThresholdLogTwo : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    (∃ k : ℕ → ℕ, Tendsto (fun N : ℕ => (k N : ℝ) / Real.logb 2 N) atTop (nhds 1) ∧
      ∀ (G : ℕ → Type) [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)],
        Tendsto (fun i => Fintype.card (G i)) atTop atTop →
          Tendsto (fun i => balancedProbability (G i) ε (k (Fintype.card (G i)))) atTop (nhds 1)) ∧
    ∀ (G : Type) [AddCommGroup G] [Fintype G] (A : Finset G), IsBalanced ε A →
      Fintype.card G ≤ 2 ^ A.card

/--
**Erdős Problem 1179 holds.** For every real $\varepsilon$ with $0 < \varepsilon < 1$, the
following two bounds hold. Upper bound: there is a function $k : \mathbb{N} \to \mathbb{N}$ with
$k(N) / \log_2 N \to 1$ as $N \to \infty$ such that, for every sequence $(G_i)_{i \in \mathbb{N}}$
of finite abelian groups with $|G_i| \to \infty$, the probability that a uniformly random
$k(|G_i|)$-element subset of $G_i$ is $\varepsilon$-balanced tends to $1$ as $i \to \infty$. Lower
bound: for every finite abelian group $G$, every $\varepsilon$-balanced subset $A \subseteq G$
satisfies $|G| \le 2^{|A|}$.

Writing $g_\varepsilon(N)$ for the least size for which a uniformly random subset of a group of
order $N$ is $\varepsilon$-balanced with probability tending to $1$, Erdős and Hall proved
$g_\varepsilon(N) \le (1 + O_\varepsilon(\log \log \log N / \log \log N)) \log_2 N$, improving the
bound $(2 + o(1)) \log_2 N + O_\varepsilon(1)$ of Erdős and Rényi; the lower bound holds because
an $\varepsilon$-balanced set with $\varepsilon < 1$ has every element of $G$ as a subset sum.
erdosproblems.com/1179 lists the problem as proved.

Source: T. F. Bloom, Erdős Problems, Problem #1179, https://www.erdosproblems.com/1179 (status
PROVED); resolution: P. Erdős and R. R. Hall,
Probabilistic methods in group theory. II, Houston J. Math. 2 (1976), 173-180,
erdosproblems.com/1179: g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N for all 0 < ε < 1.
-/
public theorem_wanted balancedSubsetSumsThresholdLogTwo_holds : balancedSubsetSumsThresholdLogTwo

end MathlibExt.Combinatorics.RandomSubsetSumsBalancedErdosProblem1179Wanted
