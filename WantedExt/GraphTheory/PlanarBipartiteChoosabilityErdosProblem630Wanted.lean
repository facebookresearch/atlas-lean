/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# List colouring planar bipartite graphs (Erdős Problem 630)

Erdős Problem 630 (Erdős, Rubin and Taylor): does every planar bipartite graph `G` have list
chromatic number `χ_L(G) ≤ 3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Combinatorics.SimpleGraph.ListColoring
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.GraphTheory.PlanarBipartiteChoosabilityErdosProblem630Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #630, https://www.erdosproblems.com/630 (status PROVED
(LEAN)). UnsolvedMath record UM-30006958 (`EP-630`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite. Planarity is MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free straight-line
drawing), equivalent to planarity for finite simple graphs by Fáry's theorem; `χ_L(G) ≤ q` is
MathlibExt's `SimpleGraph.IsListColorable q` (every assignment of lists of at least `q` colours
admits a proper colouring from the lists).
-/

/-- Erdős Problem 630 (Erdős, Rubin and Taylor): every finite planar bipartite graph has list
chromatic number at most `3`. Planarity is `SimpleGraph.IsPlanar` (a crossing-free straight-line
drawing, equivalent to planarity for finite graphs by Fáry's theorem). -/
def planarBipartiteThreeChoosable : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsPlanar → G.IsBipartite →
    G.IsListColorable 3

/--
Resolved true: Alon and Tarsi proved that every planar bipartite graph is `3`-choosable;
erdosproblems.com/630 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#630, https://www.erdosproblems.com/630 (status PROVED (LEAN)); resolution: N. Alon and M. Tarsi,
Colorings and orientations of graphs, Combinatorica (1992), 125-134, erdosproblems.com/630: the
answer is yes, proved by Alon and Tarsi, https://www.erdosproblems.com/630.
-/
public theorem_wanted planarBipartiteThreeChoosable_holds : planarBipartiteThreeChoosable

end MathlibExt.GraphTheory.PlanarBipartiteChoosabilityErdosProblem630Wanted
