/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.StripDualBlocking

/-!
# Tests for `Sheffield.StripDualBlocking`

Module under test: `Sheffield.StripDualBlocking` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlaneEmbedding.walkArc_coord_strict_bounds_of_support` for the trivial walk at a vertex
  strictly inside the strip `(0, 4)` with arc bound `1`.
* `PeriodicPlanarDualPair.finiteStripPrimal_dualPairConnection_disjoint` elaborates (check-only;
  its geometric hypotheses need a concrete dual pair).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace StripDualBlocking

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- The arc of the trivial walk at `x` stays in the open strip `(0, 4)` (first coordinate).
example (E : PeriodicPlaneEmbedding P)
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ 1)
    (x : V) (hx : 0 + 1 < E.vertexCoord x 0 ∧ E.vertexCoord x 0 < 4 - 1) :=
  E.walkArc_coord_strict_bounds_of_support zero_le_one hB 0 (SimpleGraph.Walk.nil (u := x))
    (fun v hv => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      exact hv ▸ hx)

-- `PeriodicPlanarDualPair.finiteStripPrimal_dualPairConnection_disjoint` elaborates.
example := @PeriodicPlanarDualPair.finiteStripPrimal_dualPairConnection_disjoint

end StripDualBlocking
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
