/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small non-planar subgraphs of dense graphs (Erdős Problem 1018)

Erdős Problem 1018: let `ε > 0`. Is there a constant `C_ε` such that, for all large `n`, every graph
on `n` vertices with at least `n^{1+ε}` edges contains a subgraph on at most `C_ε` vertices which is
non-planar?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.GraphTheory.SmallNonplanarSubgraphErdosProblem1018Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1018, https://www.erdosproblems.com/1018 (status
SOLVED (LEAN)). UnsolvedMath record UM-30007127 (`EP-1018`), dataset ulamai/UnsolvedMath v1.8.0.

Planarity is `MathlibExt`'s `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing), which
for finite graphs is planarity by Fáry's theorem. Subgraphs are taken induced: a graph with a
non-planar subgraph on a vertex set has a non-planar induced subgraph there.
-/

/-- Erdős Problem 1018: for every `ε > 0` there is `C_ε` such that, for all large `n`, every graph
on `n` vertices with at least `n^{1+ε}` edges has a non-planar subgraph on at most `C_ε` vertices
(planarity is `SimpleGraph.IsPlanar`, crossing-free straight-line drawings, which by Fáry's theorem
is planarity for finite graphs; an induced subgraph is non-planar if any subgraph on its vertex set
is). -/
def smallNonplanarSubgraph : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    (n : ℝ) ^ (1 + ε) ≤ G.edgeSet.ncard →
    ∃ S : Finset (Fin n), S.card ≤ C ∧ ¬ (G.induce (S : Set (Fin n))).IsPlanar

/--
Resolved true: Kostochka and Pyber proved that such a graph contains a subdivision of `K_5`, which
is non-planar, on `O_ε(1)` vertices; erdosproblems.com/1018 lists the problem as solved. Source: T.
F. Bloom, Erdős Problems, Problem #1018, https://www.erdosproblems.com/1018 (status SOLVED (LEAN));
resolution: A. Kostochka and L. Pyber, Small topological complete subgraphs of "dense" graphs,
Combinatorica (1988), 83-86, G contains a subdivision of K_5 with O_ε(1) vertices
(erdosproblems.com/1018), https://www.erdosproblems.com/1018.
-/
public theorem_wanted smallNonplanarSubgraph_holds : smallNonplanarSubgraph

end MathlibExt.GraphTheory.SmallNonplanarSubgraphErdosProblem1018Wanted
