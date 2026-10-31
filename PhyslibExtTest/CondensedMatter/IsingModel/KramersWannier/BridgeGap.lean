/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.BridgeGap

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KramersWannier.BridgeGap`

* `jbw_vertexCut_not_even`: the boundary of the site `(0, 0)` has odd degree at `(1, 0)`;
* `jbw_mem_bdEdgeSet` unfolds membership in `jbw_bdEdgeSet`;
* the first conjunct of `jbw_jed_insufficient` is `jbw_vertexCut_not_even`;
* `jbw_hard_gap` holds for the empty walk.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.BridgeGap

open _root_.StatMech _root_.StatMech.Walls _root_.StatMech.Lattice

-- A vertex cut is not an even edge set.
example : ¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![1, 0]) :=
  jbw_vertexCut_not_even

-- Membership in the boundary-edge set is `bdEdge`.
example (S : Set (Site 2)) (e : Sym2 (Site 2)) : e ∈ jbw_bdEdgeSet S ↔ bdEdge S e :=
  jbw_mem_bdEdgeSet S e

-- The summary theorem contains the parity obstruction.
example : ¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![1, 0]) :=
  jbw_jed_insufficient.1

-- `jbw_hard_gap` holds trivially for the empty walk, which has no edges.
example (a : Site 2) : jbw_hard_gap (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a) := by
  intro u v _ h
  simp at h

end PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.BridgeGap
