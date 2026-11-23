/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tiles of two-ended highly arc transitive digraphs (Open Problem Garden 691)

Open Problem Garden, Highly arc transitive two ended digraphs (P. J. Cameron, C. E. Praeger and N.
C. Wormald): if `G` is a highly arc transitive digraph with two ends, then every tile of `G` is a
disjoint union of complete bipartite graphs.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
public import WantedExt.GraphTheory.UniversalHighlyArcTransitiveOpenGardenProblem677Wanted

@[expose] public section

namespace MathlibExt.GraphTheory.TwoEndedHighlyArcTransitiveTilesOpenGardenProblem691Wanted

/-!
Source: Open Problem Garden, Highly arc transitive two ended digraphs (node 691; P. J. Cameron, C.
E. Praeger and N. C. Wormald),
http://www.openproblemgarden.org/op/highly_arc_transitive_two_ended_digraphs. UnsolvedMath record
UM-00003305 (`OPG-691`), dataset ulamai/UnsolvedMath v1.8.0.

Digraphs, `s`-arcs and high arc transitivity are the source page's, from the Open Problem Garden 677
module, imported; a digraph with a level map as below has no 2-cycles, and on such digraphs these
`s`-arcs are DeVos-Mohar-Šámal's directed walks (Section 1). As on the source page the digraph is
connected (its underlying undirected graph is, and the page's tiles come from Dunwoody's theorem for
connected graphs) and has two ends (Mathlib's `SimpleGraph.end` of the underlying graph has two
elements). The page's system of imprimitivity `{X_i}` with every edge between consecutive blocks is
encoded by a level map `b : V → ℤ` with finite levels and every arc from level `i` to level `i + 1`;
DeVos-Mohar-Šámal (Proposition 4.1) show this `ℤ`-system is unique, and since every arc raises the
level by one, `b` is determined by `D` up to a shift on a connected digraph. The tile at `i` is the
bipartite digraph of arcs from level `i` to level `i + 1`; it is a disjoint union of complete
bipartite graphs exactly when it has no induced path `u' → v ← u → v'`, i.e. when `u → v`, `u' → v`
and `u → v'` force `u' → v'`.
-/

open MathlibExt.GraphTheory.UniversalHighlyArcTransitiveOpenGardenProblem677Wanted

/-- The conjecture of Cameron, Praeger and Wormald: in a connected highly arc transitive digraph
`D` with two ends, every tile is a disjoint union of complete bipartite graphs. The tiles are read
off a level map `b : V → ℤ` with finite levels such that every arc goes from some level `i` to level
`i + 1` (the `ℤ`-system of blocks, unique by DeVos-Mohar-Šámal, Proposition 4.1); the tile at `i`
consists of the arcs from level `i` to level `i + 1`, and it is a disjoint union of complete
bipartite graphs exactly when `u → v`, `u' → v` and `u → v'` force `u' → v'`. Connectivity and ends
are those of the underlying undirected graph. -/
def twoEndedTilesCompleteBipartite : Prop :=
  ∀ (V : Type) (D : Digraph V), (SimpleGraph.fromRel D.Adj).Connected →
    (SimpleGraph.fromRel D.Adj).end.ncard = 2 → IsHighlyArcTransitive D →
    ∀ b : V → ℤ, (∀ u v, D.Adj u v → b v = b u + 1) → (∀ i, {v | b v = i}.Finite) →
      ∀ (i : ℤ) (u u' v v' : V), b u = i → b u' = i → b v = i + 1 → b v' = i + 1 →
        D.Adj u v → D.Adj u' v → D.Adj u v' → D.Adj u' v'

/--
Resolved false: DeVos, Mohar and Šámal constructed connected two-ended highly arc transitive
digraphs (Construction 2 with the alternately oriented 6-cycle as template) whose tiles are not
disjoint unions of complete bipartite graphs, as Cameron, Praeger and Wormald had conjectured
impossible. Source: Open Problem Garden, Highly arc transitive two ended digraphs (node 691; P. J.
Cameron, C. E. Praeger and N. C. Wormald),
http://www.openproblemgarden.org/op/highly_arc_transitive_two_ended_digraphs; resolution: M. DeVos,
B. Mohar and R. Šámal, Highly arc-transitive digraphs - structure and counterexamples, Combinatorica
35 (2015), 553-571, doi:10.1007/s00493-014-3040-4; arXiv:1110.2945, Section 3: Construction 2 with
template T the alternately oriented 6-cycle (K_{3,3} minus a matching) gives a two-ended highly
arc-transitive digraph (Theorem 3.2) whose tile is not a disjoint union of complete bipartite
digraphs, a counterexample to Cameron-Praeger-Wormald's Conjecture 3.1; abstract: 'constructions of
2-ended highly arc transitive digraphs where each building block is a finite bipartite graph that is
not a disjoint union of complete bipartite graphs. This was conjectured impossible'; Proposition
4.1: the Z-system is unique, https://doi.org/10.1007/s00493-014-3040-4.
-/
public theorem_wanted twoEndedTilesCompleteBipartite_refuted : ¬ twoEndedTilesCompleteBipartite

end MathlibExt.GraphTheory.TwoEndedHighlyArcTransitiveTilesOpenGardenProblem691Wanted
