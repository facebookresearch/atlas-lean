/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterRunsAxisFE
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerCorridors
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttach
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting
public import MathlibExt.Combinatorics.SimpleGraph.Menger.MengerSplice

/-!
# Clusters meeting an axis corridor

A cluster connected without the origin to a cell of an axis corridor reaches the corridor mouth
after forcing, which gives the axis routing premise, ray reaching and axis assignment.

## i. Overview

After forcing the corridor along `j` and removing the origin, the mouth `e_j` is connected to every
cell. `cnp_ClusterMeetsCorridor ω x j L` asks that `x` be connected without the origin to a cell of
the corridor and have an infinite cut cluster after forcing. It gives the axis routing premise, ray
reaching (through a simple path from the mouth) and axis assignment. Corridor cells and the axis
neighbour satisfy it, and an infinite cut cluster reaches sites with large coordinates.

The Burton–Keane theorem that combined this with the counting hypotheses of
`burton_keane_uniqueness_full` was removed as vacuous: those hypotheses are jointly refuted for
`d ≥ 1` by `tfc_not_hbound_hdens`.

## ii. Key results

- `cnp_clusterReachesRay_of_clusterMeetsCorridor` : ray reaching from meeting the corridor.

## iii. Table of contents

- A. The corridor mouth
- B. Meeting the corridor
- C. Examples

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Combinatorics

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. The corridor mouth -/

/-- Same statement as `bc2_forcedPathConn`; kept because `ForcedPathChain` is not imported by all
its
users. -/
lemma cnp_mouth_connected_corridorCell (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1) :
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) :=
  mco_corridorVert_connected ω j (L + 1) m hm1 hmL

lemma cnp_removeSite_le (ω : ConfigSpace (Sym2 (Site d))) (z : Site d) :
    removeSite z ω ≤ ω := by
  intro e
  by_cases h : z ∈ e
  · rw [removeSite_apply_of_mem h]; exact bot_le
  · rw [removeSite_apply_of_notMem h]

/-! ## B. Meeting the corridor -/

/-- The cluster of `x` meets the corridor along `j`: `x` is connected without the origin to some
cell
`m e_j` with `1 ≤ m ≤ L + 1`, and its cut cluster after forcing the corridor is infinite. -/
def cnp_ClusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (L : ℕ) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ m ≤ L + 1 ∧
    Connected d (removeSite 0 ω) x (hrHD_rayPt j (m : ℤ))) ∧
  (cluster d (removeSite 0 ω) x).Infinite

lemma cnp_axisRoutingPremise_of_clusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : cnp_ClusterMeetsCorridor ω x j L) :
    craf_AxisRoutingPremise ω x j L := by
  obtain ⟨⟨m, hm1, hmL, hmeet⟩, hinf⟩ := h
  set ω' := forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω with hω'
  have hle : removeSite 0 ω ≤ removeSite 0 ω' := lma_removeSite_le_forceOpen ω _
  have hmeet' : Connected d (removeSite 0 ω') x (hrHD_rayPt j (m : ℤ)) :=
    connected_mono hle hmeet
  have hcorr : Connected d (removeSite 0 ω') (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) :=
    cnp_mouth_connected_corridorCell ω j L m hm1 hmL
  have hcut : Connected d (removeSite 0 ω') x (hrHD_rayPt j 1) := hmeet'.trans hcorr.symm
  have hnear : Connected d ω' x (hrHD_rayPt j 1) :=
    connected_mono (cnp_removeSite_le ω' 0) hcut
  have hinf' : (cluster d (removeSite 0 ω') x).Infinite := hinf.mono (cluster_mono hle x)
  exact ⟨hnear, hcut, hinf'⟩

lemma cnp_mouth_attachment_isPath (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (x : Site d) (m : ℕ)
    (pA : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk
      x (hrHD_rayPt j (m : ℤ)))
    (pB : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk
      (hrHD_rayPt j (m : ℤ)) (hrHD_rayPt j 1))
    (hpA : pA.IsPath) (hpB : pB.IsPath)
    (hmeet : ∀ z, z ∈ pA.support → z ∈ pB.support → z = hrHD_rayPt j (m : ℤ)) :
    (pA.append pB).IsPath :=
  mgs_append_isPath hpA hpB hmeet

lemma cnp_exists_simplePath_mouth (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (x : Site d) (m : ℕ)
    (pA : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk
      x (hrHD_rayPt j (m : ℤ)))
    (pB : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk
      (hrHD_rayPt j (m : ℤ)) (hrHD_rayPt j 1))
    (hpA : pA.IsPath) (hpB : pB.IsPath)
    (hmeet : ∀ z, z ∈ pA.support → z ∈ pB.support → z = hrHD_rayPt j (m : ℤ)) :
    ∃ p : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk
      x (hrHD_rayPt j 1), p.IsPath :=
  ⟨pA.append pB, cnp_mouth_attachment_isPath ω j L x m pA pB hpA hpB hmeet⟩

lemma cnp_clusterReachesRay_of_clusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : cnp_ClusterMeetsCorridor ω x j L) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  craf_clusterReachesRay_of_insertion ω x j L
    (cnp_axisRoutingPremise_of_clusterMeetsCorridor ω x j L h)

lemma cnp_axisAssignment_of_clusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : cnp_ClusterMeetsCorridor ω x j L) :
    crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  craf_axisAssignment_of_insertion ω x j L
    (cnp_axisRoutingPremise_of_clusterMeetsCorridor ω x j L h)

/-! ## C. Examples -/

lemma cnp_clusterMeetsCorridor_corridorCell (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j (m : ℤ))).Infinite) :
    cnp_ClusterMeetsCorridor ω (hrHD_rayPt j (m : ℤ)) j L :=
  ⟨⟨m, hm1, hmL, connected_rfl⟩, hinf⟩

lemma cnp_axisRoutingPremise_corridorCell (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j (m : ℤ))).Infinite) :
    craf_AxisRoutingPremise ω (hrHD_rayPt j (m : ℤ)) j L :=
  cnp_axisRoutingPremise_of_clusterMeetsCorridor ω (hrHD_rayPt j (m : ℤ)) j L
    (cnp_clusterMeetsCorridor_corridorCell ω j L m hm1 hmL hinf)

lemma cnp_clusterMeetsCorridor_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    cnp_ClusterMeetsCorridor ω (hrHD_rayPt j 1) j L := by
  have h := cnp_clusterMeetsCorridor_corridorCell ω j L 1 le_rfl (by omega) (by
    simpa using hinf)
  simpa using h

/-- Same statement as `bc_cutUnbounded_coord`; kept because `CutUnboundedCoordinate` is not imported
by
all its users. -/
lemma cnp_cut_someAxis_reach_of_infinite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y :=
  crr_infinite_reaches_far_coord (removeSite 0 ω) x hinf n

end Percolation

end StatMech
