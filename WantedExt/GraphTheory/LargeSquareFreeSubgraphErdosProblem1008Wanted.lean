/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Large `C₄`-free subgraphs (Erdős Problem 1008)

Erdős Problem 1008: does every graph with `m` edges contain a subgraph with `≫ m^{2/3}` edges which
contains no `C₄`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

namespace MathlibExt.GraphTheory.LargeSquareFreeSubgraphErdosProblem1008Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1008, https://www.erdosproblems.com/1008 (status
PROVED (LEAN)). UnsolvedMath record UM-30007122 (`EP-1008`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite. A `C₄`-free subgraph is `H ≤ G` with `(cycleGraph 4).Free H`. `≫ m^{2/3}` is `≥ c
m^{2/3}` for an absolute `c > 0`. Compared with the formal-conjectures statement
`ErdosProblems/1008.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 1008: there is `c > 0` such that every finite graph with `m` edges has a
subgraph with at least `c m^{2/3}` edges and no `4`-cycle. -/
def squareFreeSubgraphTwoThirds : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    ∃ H ≤ G, (SimpleGraph.cycleGraph 4).Free H ∧
      c * (G.edgeSet.ncard : ℝ) ^ ((2 : ℝ) / 3) ≤ H.edgeSet.ncard

/--
Resolved true: Conlon, Fox and Sudakov proved that every graph with `m` edges has a `C₄`-free
subgraph with `≫ m^{2/3}` edges; erdosproblems.com/1008 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #1008, https://www.erdosproblems.com/1008 (status PROVED (LEAN));
resolution: D. Conlon, J. Fox and B. Sudakov, Large subgraphs without complete bipartite graphs,
arXiv:1401.6711 (2014), affirmative answer (erdosproblems.com/1008; a short proof by Hunter in the
comments), https://arxiv.org/abs/1401.6711.
-/
public theorem_wanted squareFreeSubgraphTwoThirds_holds : squareFreeSubgraphTwoThirds

end MathlibExt.GraphTheory.LargeSquareFreeSubgraphErdosProblem1008Wanted
