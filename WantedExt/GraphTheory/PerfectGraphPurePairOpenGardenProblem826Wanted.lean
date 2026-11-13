/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complete bipartite subgraphs of perfect graphs (Open Problem Garden 826)

Open Problem Garden, Complete bipartite subgraphs of perfect graphs (J. Fox): let `G` be a perfect
graph on `n` vertices. Is it true that either `G` or its complement contains a complete bipartite
subgraph with bipartition `(A, B)` such that `|A|, |B| ≥ n^{1 - o(1)}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph

@[expose] public section

namespace MathlibExt.GraphTheory.PerfectGraphPurePairOpenGardenProblem826Wanted

/-!
Source: Open Problem Garden, Complete bipartite subgraphs of perfect graphs (node 826; J. Fox),
http://www.openproblemgarden.org/op/complete_bipartite_subgraphs_of_perfect_graphs. UnsolvedMath
record UM-00003153 (`OPG-826`), dataset ulamai/UnsolvedMath v1.8.0.

A complete bipartite subgraph of `G` or of its complement with sides `A`, `B` is a pure pair:
disjoint vertex sets with `A` complete or anticomplete to `B`. The bound `n^{1 - o(1)}` is read as
in the resolving paper, which states Fox's conjecture as: for every `c > 0` there is `ε > 0` such
that every perfect graph with `n > 1` vertices has a pure pair with `|A|, |B| ≥ ε n^{1 - c}`.
Perfect is `MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect`: every induced
subgraph has chromatic number equal to its clique number.
-/

/-- Fox's conjecture, as stated by Scott-Seymour-Spirkl: for every `c > 0` there is `ε > 0` such
that every perfect graph `G` with `n > 1` vertices has a pure pair `A, B` (disjoint vertex sets with
`A` complete or anticomplete to `B`, that is, a complete bipartite subgraph of `G` or of its
complement) with `|A|, |B| ≥ ε n^{1 - c}`. -/
def perfectGraphsHaveLargePurePairs : Prop :=
  ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect G →
    1 < Fintype.card V → ∃ A B : Finset V, Disjoint A B ∧
      ε * (Fintype.card V : ℝ) ^ (1 - c) ≤ A.card ∧ ε * (Fintype.card V : ℝ) ^ (1 - c) ≤ B.card ∧
      ((∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∨ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)

/--
Resolved true: Scott, Seymour and Spirkl prove Fox's conjecture: for every `c > 0` there is `ε > 0`
such that every perfect graph with `n > 1` vertices has a pure pair `A, B` with
`|A|, |B| ≥ ε n^{1 - c}`, so `G` or its complement contains the complete bipartite graph with sides
`A` and `B`. Source: Open Problem Garden, Complete bipartite subgraphs of perfect graphs (node 826;
J. Fox), http://www.openproblemgarden.org/op/complete_bipartite_subgraphs_of_perfect_graphs;
resolution: A. Scott, P. Seymour and S. Spirkl, Pure pairs. V. Excluding some long subdivision,
Combinatorica 43 (2023), 571-593; arXiv:2105.03956, abstract: Fox proved that for all c > 0 there is
ε > 0 such that every comparability graph with n > 1 vertices has a pure pair A, B with |A|, |B| ≥ ε
n^(1-c), and conjectured the same for every perfect graph; 'We prove this conjecture and strengthen
it in several ways', https://doi.org/10.1007/s00493-023-00025-8.
-/
public theorem_wanted perfectGraphsHaveLargePurePairs_holds : perfectGraphsHaveLargePurePairs

end MathlibExt.GraphTheory.PerfectGraphPurePairOpenGardenProblem826Wanted
