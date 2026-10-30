/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterReachesRay
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorConnect
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AxisAssignment

/-!
# Clusters running along an axis meet the corridor

A cluster running along an axis meets the axis corridor, satisfies the axis routing premise and
reaches the ray after forcing the corridor.

## i. Overview

If the cluster of `x` runs along axis `j` (`crr_ClusterRunsAlongAxis`), it meets every corridor
along `j`, satisfies `craf_AxisRoutingPremise`, reaches the ray after forcing the corridor, and is
connected to the neighbour `e_j` without cutting.

The Burton–Keane theorem that combined this with the counting hypotheses of
`burton_keane_uniqueness_full` was removed as vacuous: those hypotheses are jointly refuted for
`d ≥ 1` by `tfc_not_hbound_hdens`.

## ii. Key results

- `cmc_clusterReachesRay_of_runsAlongAxis` : the cluster reaches the ray after forcing the corridor.

## iii. Table of contents

- A. Running along an axis

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Running along an axis -/

lemma cmc_clusterMeetsCorridor_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : crr_ClusterRunsAlongAxis ω x j) :
    cnp_ClusterMeetsCorridor ω x j L := by
  obtain ⟨L', _, _, hcut, hinf⟩ := h
  refine ⟨⟨1, le_rfl, by omega, ?_⟩, hinf⟩
  simpa using hcut

lemma cmc_axisRoutingPremise_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : crr_ClusterRunsAlongAxis ω x j) :
    craf_AxisRoutingPremise ω x j L :=
  cnp_axisRoutingPremise_of_clusterMeetsCorridor ω x j L
    (cmc_clusterMeetsCorridor_of_runsAlongAxis ω x j L h)

lemma cmc_clusterReachesRay_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : crr_ClusterRunsAlongAxis ω x j) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  cnp_clusterReachesRay_of_clusterMeetsCorridor ω x j L
    (cmc_clusterMeetsCorridor_of_runsAlongAxis ω x j L h)

lemma cmc_runsAlongAxis_entails_uncut_connection (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    Connected d ω x (hrHD_rayPt j 1) := by
  obtain ⟨_, _, huncut, _, _⟩ := h
  exact huncut

end Percolation

end StatMech
