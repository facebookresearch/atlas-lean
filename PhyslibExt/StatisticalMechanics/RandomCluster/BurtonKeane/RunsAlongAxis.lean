/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Sym.Sym2
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterRunsAxisFE
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterMeetsCorridor
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AxisAssignment
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedPathChain
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.WiringForcesOpen

/-!
# Clusters running along an axis

A cluster whose opened axis corridor stays infinite after removing the origin reaches the ray and
meets the corridor.

## i. Overview

If the cluster of `e_j` in the configuration with the axis corridor opened and the origin removed is
infinite, then the cluster reaches the axis ray far out, meets the corridor and runs along the axis.
These are the inputs of the axis-assignment route to a trifurcation precursor at the origin.

## ii. Key results

- `rap_runsAlongAxis_ray` : the cluster runs along the axis
- `rap_clusterReachesRay_ray` : the cluster reaches the axis ray

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma rap_runsAlongAxis_ray (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    (∀ t : ℕ, t < L → forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω
        s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true) ∧
      crr_ClusterRunsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
        (hrHD_rayPt j 1) j := by
  refine ⟨fun t ht => Walls.bc_wiring_forces_open_eq_true ω j L t ht, ?_⟩
  exact craf_clusterRunsAlongAxis_of_insertion ω (hrHD_rayPt j 1) j L
    (craf_axisRoutingPremise_neighbour ω j L hinf)

lemma rap_clusterReachesRay_ray (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
      (hrHD_rayPt j 1) j :=
  crr_clusterReachesRay_of_runsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
    (hrHD_rayPt j 1) j (rap_runsAlongAxis_ray ω j L hinf).2

lemma rap_clusterMeetsCorridor_ray (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L L' : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    cnp_ClusterMeetsCorridor (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
      (hrHD_rayPt j 1) j L' :=
  cmc_clusterMeetsCorridor_of_runsAlongAxis
    (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j L'
    (rap_runsAlongAxis_ray ω j L hinf).2

lemma rap_ray_open_edge_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hL : 1 ≤ L) :
    forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω
      s(hrHD_rayPt j (((0 : ℕ) : ℤ) + 1), hrHD_rayPt j (((0 : ℕ) : ℤ) + 2)) = true :=
  Walls.bc_wiring_forces_open_eq_true ω j L 0 (by omega)

lemma rap_runsAlongAxis_entails_near_connection (ω : ConfigSpace (Sym2 (Site d)))
    (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    Connected d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1)
      (hrHD_rayPt j 1) :=
  cmc_runsAlongAxis_entails_uncut_connection
    (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j
    (rap_runsAlongAxis_ray ω j L hinf).2

end Percolation

end StatMech
