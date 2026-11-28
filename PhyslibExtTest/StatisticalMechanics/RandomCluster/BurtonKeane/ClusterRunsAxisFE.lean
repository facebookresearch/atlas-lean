/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterRunsAxisFE

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterRunsAxisFE`

* `craf_mem_corridorEdges` places a concrete axis edge in the corridor (`d = 1`, `L = 2`);
* `craf_clusterRunsAlongAxis_of_insertion` and `craf_clusterReachesRay_of_insertion` applied to a
  routing premise;
* `craf_axisRoutingPremise_neighbour` applied to the neighbour of the origin.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterRunsAxisFE

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- The first axis edge of `Site 1` lies in the corridor of length `3`.
example : s(hrHD_rayPt (0 : Fin 1) ((0 : ℕ) + 1), hrHD_rayPt (0 : Fin 1) ((0 : ℕ) + 2)) ∈
    hrHD_corridorEdges (0 : Fin 1) (2 + 1) :=
  craf_mem_corridorEdges 0 2 (by norm_num)

-- A routing premise yields a cluster running along the axis after forcing the corridor.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) (L : ℕ)
    (h : craf_AxisRoutingPremise ω x j L) :
    crr_ClusterRunsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  craf_clusterRunsAlongAxis_of_insertion ω x j L h

-- A routing premise yields a cluster reaching the ray after forcing the corridor.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) (L : ℕ)
    (h : craf_AxisRoutingPremise ω x j L) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  craf_clusterReachesRay_of_insertion ω x j L h

-- The neighbour of the origin satisfies the routing premise when its cluster is infinite.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    craf_AxisRoutingPremise ω (hrHD_rayPt j 1) j L :=
  craf_axisRoutingPremise_neighbour ω j L hinf

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterRunsAxisFE
