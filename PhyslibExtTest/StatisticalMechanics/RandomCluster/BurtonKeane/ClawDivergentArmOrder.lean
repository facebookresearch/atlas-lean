/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder`

* `stac_claw_shadow_consistent`: the finite claw shadow is consistent;
* `stac_removeSites_cluster_singleton`: a removed site is a singleton cluster (all-open
  configuration);
* `stac_not_divergentArmOrder_of_claw` in conditional form;
* `stac_uniform_divergentArmOrder_false` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- The claw shadow is consistent.
example := stac_claw_shadow_consistent

-- A removed site forms a singleton cluster.
example : cluster 2 (removeSites {0} (fun _ => true)) 0 = {0} :=
  stac_removeSites_cluster_singleton {0} _ (Finset.mem_singleton_self 0)

-- A claw configuration excludes the divergent arm order.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hclaw : stac_ClawConfig ω n) :
    ¬ fsp_DivergentArmOrder ω n :=
  stac_not_divergentArmOrder_of_claw ω n hclaw

-- The uniform refutation from one claw, by type.
example := @stac_uniform_divergentArmOrder_false

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder
