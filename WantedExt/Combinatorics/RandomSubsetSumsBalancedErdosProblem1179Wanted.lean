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
/-- `F_A(g)`: the number of subsets of `A` with sum `g`. -/
noncomputable def subsetSumCount {G : Type*} [AddCommGroup G] (A : Finset G) (g : G) : ℕ :=
  (A.powerset.filter fun S => ∑ x ∈ S, x = g).card

/-- `A` is `ε`-balanced: `|F_A(g) - 2^{|A|}/N| ≤ ε 2^{|A|}/N` for every `g`, where `N = |G|`. -/
def IsBalanced {G : Type*} [AddCommGroup G] [Fintype G] (ε : ℝ) (A : Finset G) : Prop :=
  ∀ g : G, |(subsetSumCount A g : ℝ) - 2 ^ A.card / Fintype.card G| ≤
    ε * (2 ^ A.card / Fintype.card G)

open scoped Classical in
/-- The probability that a uniformly random `k`-element subset of `G` is `ε`-balanced. -/
noncomputable def balancedProbability (G : Type*) [AddCommGroup G] [Fintype G] (ε : ℝ) (k : ℕ) :
    ℝ :=
  (((univ : Finset G).powersetCard k).filter (IsBalanced ε)).card /
    ((univ : Finset G).powersetCard k).card

/-- Erdős Problem 1179: `g_ε(N) = (1 + o(1)) log₂ N` for every `ε ∈ (0, 1)`. Upper bound: there are
sizes `k(N) = (1 + o(1)) log₂ N` such that, along every sequence of finite abelian groups with
`|G| → ∞`, a uniformly random `k(|G|)`-subset is `ε`-balanced with probability tending to `1`.
Lower bound: every `ε`-balanced subset `A` of a finite abelian group `G` has `|G| ≤ 2^{|A|}`. -/
def balancedSubsetSumsThresholdLogTwo : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    (∃ k : ℕ → ℕ, Tendsto (fun N : ℕ => (k N : ℝ) / Real.logb 2 N) atTop (nhds 1) ∧
      ∀ (G : ℕ → Type) [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)],
        Tendsto (fun i => Fintype.card (G i)) atTop atTop →
          Tendsto (fun i => balancedProbability (G i) ε (k (Fintype.card (G i)))) atTop (nhds 1)) ∧
    ∀ (G : Type) [AddCommGroup G] [Fintype G] (A : Finset G), IsBalanced ε A →
      Fintype.card G ≤ 2 ^ A.card

/--
Resolved true: Erdős and Hall proved `g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N` for
every `0 < ε < 1`, improving Erdős and Rényi's `(2 + o(1)) log₂ N + O_ε(1)`; the lower bound `g_ε(N)
≥ log₂ N` holds since an `ε`-balanced `A` with `ε < 1` has every `g` as a subset sum, so `2^{|A|} ≥
N`. erdosproblems.com/1179 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#1179, https://www.erdosproblems.com/1179 (status PROVED); resolution: P. Erdős and R. R. Hall,
Probabilistic methods in group theory. II, Houston J. Math. 2 (1976), 173-180,
erdosproblems.com/1179: g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N for all 0 < ε < 1.
-/
public theorem_wanted balancedSubsetSumsThresholdLogTwo_holds : balancedSubsetSumsThresholdLogTwo

end MathlibExt.Combinatorics.RandomSubsetSumsBalancedErdosProblem1179Wanted
