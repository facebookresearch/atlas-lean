/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorConnect

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorConnect`

In the plane:
* `cnp_mouth_connected_corridorCell`: after forcing the axis-`0` corridor and removing the origin,
  the mouth is connected to the corridor cell at distance `2` (all-closed configuration);
* `cnp_removeSite_le` for the all-open configuration;
* `cnp_clusterMeetsCorridor_neighbour` and `cnp_clusterReachesRay_of_clusterMeetsCorridor` in
  conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorConnect

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- The corridor mouth is connected to the corridor cell at distance `2`.
example : Connected 2 (removeSite 0 (forceOpenFinset (hrHD_corridorEdges (0 : Fin 2) (3 + 1))
    closed2)) (hrHD_rayPt 0 1) (hrHD_rayPt 0 ((2 : ℕ) : ℤ)) :=
  cnp_mouth_connected_corridorCell closed2 0 3 2 (by norm_num) (by norm_num)

-- Removing a site only closes edges.
example : removeSite (0 : Site 2) (fun _ => true) ≤ fun _ => true :=
  cnp_removeSite_le _ _

-- An infinite cut cluster at the mouth meets the corridor and so reaches the ray.
example (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ)
    (hinf : (cluster 2 (removeSite 0 ω) (hrHD_rayPt (0 : Fin 2) 1)).Infinite) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges (0 : Fin 2) (L + 1)) ω)
      (hrHD_rayPt 0 1) 0 :=
  cnp_clusterReachesRay_of_clusterMeetsCorridor ω _ 0 L
    (cnp_clusterMeetsCorridor_neighbour ω 0 L hinf)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorConnect
