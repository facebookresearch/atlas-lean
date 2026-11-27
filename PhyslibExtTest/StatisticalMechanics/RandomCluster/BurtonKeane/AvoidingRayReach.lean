/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingRayReach

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingRayReach`

* `ray34_avoidReach_refl` and `ray34_avoidCluster_empty_eq_cluster` on explicit data;
* `ray34_Tavoiding_ray_of_infinite_cluster` applied to the explicit infinite ray cluster
  `arc_arm_ambient_infinite` of `arc_rayConfig`, avoiding `{arc_p 0}`;
* `ray34_konig` and `bc34_TavoidingRayData_of_globalCutArm` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingRayReach

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- A vertex outside `S` reaches itself.
example : ray34_AvoidReach (⊥ : SimpleGraph (Fin 3)) {1} 0 0 :=
  ray34_avoidReach_refl _ _ (by decide)

-- With no avoided set the avoiding cluster is the open cluster.
example (v : Site 2) :
    ray34_AvoidCluster (openSubgraph 2 (fun _ => true)) ∅ v = cluster 2 (fun _ => true) v :=
  ray34_avoidCluster_empty_eq_cluster _ v

-- The explicit infinite ray cluster contains a ray avoiding `{arc_p 0}`.
example := ray34_Tavoiding_ray_of_infinite_cluster arc_rayConfig arc_arm_ambient_infinite
  {arc_p 0}

-- König's lemma and the global-cut route, by type.
example := @ray34_konig
example := @bc34_TavoidingRayData_of_globalCutArm

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingRayReach
