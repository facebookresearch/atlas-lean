/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterMeetsCorridor

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterMeetsCorridor`

* `cmc_clusterMeetsCorridor_of_runsAlongAxis` and `cmc_axisRoutingPremise_of_runsAlongAxis`
  in conditional form;
* `cmc_clusterReachesRay_of_runsAlongAxis` applied to the neighbour of the origin (running along
  the axis via `crr_runsAlongAxis_of_neighbour`);
* `cmc_runsAlongAxis_entails_uncut_connection` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterMeetsCorridor

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Running along an axis meets the corridor and satisfies the routing premise.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) (L : ℕ)
    (h : crr_ClusterRunsAlongAxis ω x j) : cnp_ClusterMeetsCorridor ω x j L :=
  cmc_clusterMeetsCorridor_of_runsAlongAxis ω x j L h
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) (L : ℕ)
    (h : crr_ClusterRunsAlongAxis ω x j) : craf_AxisRoutingPremise ω x j L :=
  cmc_axisRoutingPremise_of_runsAlongAxis ω x j L h

-- The neighbour of the origin reaches the ray after forcing the corridor.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j :=
  cmc_clusterReachesRay_of_runsAlongAxis ω _ j L (crr_runsAlongAxis_of_neighbour ω j hinf)

-- Running along an axis connects to `e_j`.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (h : crr_ClusterRunsAlongAxis ω x j) : Connected d ω x (hrHD_rayPt j 1) :=
  cmc_runsAlongAxis_entails_uncut_connection ω x j h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterMeetsCorridor
