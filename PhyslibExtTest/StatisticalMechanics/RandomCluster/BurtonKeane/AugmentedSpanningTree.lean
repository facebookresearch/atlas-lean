/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AugmentedSpanningTree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AugmentedSpanningTree`

* `bsk_augG_acyclic`: one vertex with two pendant leaves is acyclic;
* `bsk_augG_leaf_deg_one`: a pendant leaf has degree one (same instance);
* `bsk_bk_count_of_connectedForest` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AugmentedSpanningTree

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- One vertex with two pendant leaves is acyclic.
example : (bsk_augG (⊥ : SimpleGraph (Fin 1)) (fun _ : Fin 2 => 0)).IsAcyclic :=
  bsk_augG_acyclic _ _ SimpleGraph.isAcyclic_bot

-- A pendant leaf has degree one.
example : (bsk_augG (⊥ : SimpleGraph (Fin 1)) (fun _ : Fin 2 => 0)).degree (Sum.inr 0) = 1 :=
  bsk_augG_leaf_deg_one _ _ 0

-- Connected forest data for all configurations gives the genuine count bound.
example {d : ℕ} (L R : ℕ) (hdata : ∀ ω : ConfigSpace (Sym2 (Site d)),
    bsk_ConnectedForestData ω L R) (ω : ConfigSpace (Sym2 (Site d))) :
    (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  bsk_bk_count_of_connectedForest L R hdata ω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AugmentedSpanningTree
