/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CrossingGluing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CrossingGluing`

* in the all-open configuration of the square lattice, the origin and `(1, 0)` are open
  neighbors, and `openSubgraphAmbientHom` maps that open edge to a lattice edge between the same
  vertices;
* `overlapCrossings_glue_horizontal` for an arbitrary embedding with edge-arc bound `B = 1`, on the
  rectangles `[0, 30] × [4, 16]` and `[10, 40] × [4, 16]` overlapping in `[14, 26] × [0, 20]`;
* `openSub_rectRestrict_eq_induce_gluing` on the unit square for an arbitrary embedding.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CrossingGluing

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice

/-- The origin and `(1, 0)` are open neighbors in the all-open configuration. -/
theorem allOpen_adj : (square.openSubgraph fun _ => true).Adj (0 : Site 2) ![1, 0] := by
  rw [PeriodicGraph.openSubgraph_adj]
  refine ⟨?_, rfl⟩
  change (hypercubicLattice 2).Adj _ _
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

-- The ambient homomorphism sends the open edge to a lattice edge with the same endpoints.
example : square.graph.Adj (square.openSubgraphAmbientHom (fun _ => true) 0)
    (square.openSubgraphAmbientHom (fun _ => true) ![1, 0]) := by
  rw [PeriodicGraph.openSubgraphAmbientHom_apply, PeriodicGraph.openSubgraphAmbientHom_apply]
  exact (square.openSubgraphAmbientHom fun _ => true).map_adj allOpen_adj

-- Gluing two overlapping horizontal crossings across a vertical crossing (`B = 1`).
example {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}
    (E : PeriodicPlaneEmbedding P)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ 1) :
    E.horizontalCrossingEvent 0 30 (0 + 4 * 1) (20 - 4 * 1) ∩
      (E.horizontalCrossingEvent 10 40 (0 + 4 * 1) (20 - 4 * 1) ∩
        E.verticalCrossingEvent (10 + 4 * 1) (30 - 4 * 1) 0 20) ⊆
      E.horizontalCrossingEvent 0 40 0 20 :=
  E.overlapCrossings_glue_horizontal one_pos hB (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- The open subgraph of a rectangle is the induced open subgraph.
example {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) :
    FK.openSub (E.rectGraph 0 1 0 1) (E.rectRestrict 0 1 0 1 omega) =
      (P.openSubgraph omega).induce (E.rectVertices 0 1 0 1) :=
  E.openSub_rectRestrict_eq_induce_gluing 0 1 0 1 omega

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CrossingGluing
