/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Saturated planar subgraphs above the Turán number (Erdős Problem 1019)

Erdős Problem 1019: a planar graph on `n` vertices with `3 n - 6` edges is called saturated. Does
every graph on `n` vertices with `⌊n² / 4⌋ + ⌊(n + 1) / 2⌋` edges contain a saturated planar graph
with more than `3` vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.GraphTheory.SaturatedPlanarSubgraphErdosProblem1019Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1019, https://www.erdosproblems.com/1019 (status
PROVED (LEAN)). UnsolvedMath record UM-30007128 (`EP-1019`), dataset ulamai/UnsolvedMath v1.8.0.

Planarity is `MathlibExt`'s `SimpleGraph.IsPlanar` (straight-line drawings, planarity for finite
graphs by Fáry's theorem). "Contains" means a copy: an injective vertex map carrying edges to edges.
The graph is nonempty (`0 < n`): the graph with no vertices has `⌊0² / 4⌋ + ⌊1 / 2⌋ = 0` edges and
contains nothing on more than `3` vertices. For `1 ≤ n ≤ 3` the edge count exceeds `n (n - 1) / 2`,
so the hypothesis is vacuous.
-/

/-- Erdős Problem 1019: every graph on `n ≥ 1` vertices with `⌊n² / 4⌋ + ⌊(n + 1) / 2⌋` edges
contains a saturated planar graph on more than `3` vertices, i.e. a copy of a planar graph `H` on
`m > 3` vertices with `3 m - 6` edges (planarity is `SimpleGraph.IsPlanar`, straight-line drawings,
which by Fáry's theorem is planarity for finite graphs). -/
def containsSaturatedPlanarGraph : Prop :=
  ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = n ^ 2 / 4 + (n + 1) / 2 →
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)) (f : Fin m ↪ Fin n), 3 < m ∧ H.IsPlanar ∧
      H.edgeSet.ncard = 3 * m - 6 ∧ ∀ i j, H.Adj i j → G.Adj (f i) (f j)

/--
Resolved true: Simonovits proved that such a graph contains `K_4` or a double pyramid `C_l + 2K_1`
(`l ≥ 3`), both saturated planar graphs; erdosproblems.com/1019 lists the problem as proved (Lean),
with Cambie's proof in its comments. Source: T. F. Bloom, Erdős Problems, Problem #1019,
https://www.erdosproblems.com/1019 (status PROVED (LEAN)); resolution: M. Simonovits, PhD thesis;
proof by S. Cambie in the erdosproblems.com/1019 comments, G contains K_4 or C_l + 2K_1 for some l ≥
3 (erdosproblems.com/1019), https://www.erdosproblems.com/1019.
-/
public theorem_wanted containsSaturatedPlanarGraph_holds : containsSaturatedPlanarGraph

end MathlibExt.GraphTheory.SaturatedPlanarSubgraphErdosProblem1019Wanted
