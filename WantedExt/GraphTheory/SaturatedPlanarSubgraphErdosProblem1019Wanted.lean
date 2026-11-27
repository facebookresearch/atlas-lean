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
No refereed proof is published. The resolution, that such a graph contains `K_4` or a double
pyramid `C_l + 2K_1` (`l ≥ 3`), both saturated planar graphs, is credited to Simonovits's PhD
thesis, cited on erdosproblems.com without a bibliographic entry; S. Cambie gave an unrefereed
proof in the erdosproblems.com/1019 comments, and the result is formalized in Lean
(plby/lean-proofs, `Erdos1019.lean`, whose `erdos_1019_sharp` states the `K_4`-or-`C_l + 2K_1`
result). erdosproblems.com/1019 lists the problem as proved (Lean) for C. Y. Ren's formalization
with topological planarity, which reuses that combinatorial core. By the erdosproblems.com/1019
discussion, Simonovits's 1975 paper (below) does not settle the problem. Source: T. F. Bloom,
Erdős Problems, Problem #1019, https://www.erdosproblems.com/1019 (status PROVED (LEAN));
resolution: M. Simonovits, PhD thesis (cited on erdosproblems.com without a bibliographic entry);
unrefereed proof by S. Cambie in the erdosproblems.com/1019 comments, G contains K_4 or C_l + 2K_1
for some l ≥ 3, https://www.erdosproblems.com/1019; formal proofs: plby/lean-proofs,
src/latest/ErdosProblems/Erdos1019.lean (`erdos_1019_sharp`), and C. Y. Ren, Lean formalization
with topological planarity (`erdos_1019_saturated_planar`), CollinYuanjieRen/awards,
submissions/jsp-000849-cyr; not settled by: M. Simonovits, On graphs not containing large
saturated planar graphs, in Infinite and Finite Sets (Keszthely, 1973), Colloq. Math. Soc. János
Bolyai 10 (1975), 1365-1386.
-/
public theorem_wanted containsSaturatedPlanarGraph_holds : containsSaturatedPlanarGraph

end MathlibExt.GraphTheory.SaturatedPlanarSubgraphErdosProblem1019Wanted
