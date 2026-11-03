/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Crosscut

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Crosscut`

* `PeriodicPlaneEmbedding.simpleWalkArc_injective_of_isPath` for a one-edge walk.
* `PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_simpleCrosscut` applied with `c = 0`,
  `d = 1`.
* `PeriodicPlanarDualPair.no_open_primal_dual_simpleWalkArc_crossing` for one-edge primal and dual
  walks that are open in a configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Crosscut

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar SimpleGraph

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- The arc of a single edge is injective.
example (E : PeriodicPlaneEmbedding P) {x y : V} (h : P.graph.Adj x y) :
    Function.Injective (E.simpleWalkArc (.cons h .nil)) :=
  E.simpleWalkArc_injective_of_isPath _ (by simp [h.ne]) Walk.not_nil_cons

-- Joined boundary arms with `c = 0 < 1 = d` contain a simple open crosscut.
example (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) (r : ℝ) (n : ℕ)
    (L R : Finset V) (h : omega ∈ E.finiteJoinedBoundaryArmEvent r 0 1 n L R) :=
  E.finiteJoinedBoundaryArmEvent_simpleCrosscut zero_lt_one h

-- An open primal edge and an open dual edge have disjoint arcs.
example (D : PeriodicPlanarDualPair P Pdual) (omega : ConfigSpace (Sym2 V)) {x y : V} {a b : W}
    (hxy : P.graph.Adj x y) (hab : Pdual.graph.Adj a b) (hp : omega s(x, y) = true)
    (hq : dualConfigEquiv D.edgeDual omega s(a, b) = true) :
    Disjoint (Set.range (D.primalEmbedding.simpleWalkArc (.cons hxy .nil)))
      (Set.range (D.dualEmbedding.simpleWalkArc (.cons hab .nil))) :=
  PeriodicPlanarDualPair.no_open_primal_dual_simpleWalkArc_crossing D omega _ _
    Walk.not_nil_cons Walk.not_nil_cons
    (fun he => by simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he; rwa [he])
    (fun he => by simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he; rwa [he])

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Crosscut
