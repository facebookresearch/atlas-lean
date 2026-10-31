/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmReachComponent

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmReachComponent`

* `arc_ambientInfinite_not_removeSiteInfinite`: an explicit configuration (`arc_rayConfig`)
  where a neighbour's cluster is infinite but finite after removing the site;
* its ingredients `arc_arm_ambient_infinite` and `arc_arm_removeSite_finite`;
* `arc_x_isolated` for the all-open configuration;
* `arc_infinite_cluster_reaches_boundary` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmReachComponent

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- The ambient cluster is infinite but the cluster after removing the site is not.
example : ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2), (openSubgraph 2 ω).Adj x a ∧
    Connected 2 ω x a ∧ (cluster 2 ω a).Infinite ∧ ¬ (cluster 2 (removeSite x ω) a).Infinite :=
  arc_ambientInfinite_not_removeSiteInfinite

-- The two halves of the witness.
example : (cluster 2 arc_rayConfig (arc_p (-1))).Infinite := arc_arm_ambient_infinite
example : (cluster 2 (removeSite (arc_p 0) arc_rayConfig) (arc_p (-1))).Finite :=
  arc_arm_removeSite_finite

-- A removed site is isolated, even in the all-open configuration.
example (y : Site 2) : ¬ (openSubgraph 2 (removeSite 0 (fun _ => true))).Adj 0 y :=
  arc_x_isolated 0 _ y

-- An infinite cluster after removing `x` reaches the boundary avoiding `x`.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) (x a : Site d)
    (hax : a ≠ x) (habox : a ∈ box d n) (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n, ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support :=
  arc_infinite_cluster_reaches_boundary ω n hn x a hax habox hinf

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmReachComponent
