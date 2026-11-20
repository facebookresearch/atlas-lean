/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Percolation.CorridorConnectProof
import Code.Walls.bkm_dccwitnessnezero

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}


















def bc_CutMeetsAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (L : ℕ) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ m ≤ L + 1 ∧
    Connected d (removeSite 0 ω) x (hrHD_rayPt j (m : ℤ))) ∧
  (cluster d (removeSite 0 ω) x).Infinite




theorem bc_cutMeetsAxis_iff_clusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) :
    bc_CutMeetsAxis ω x j L ↔ cnp_ClusterMeetsCorridor ω x j L :=
  Iff.rfl



theorem bc_clusterMeetsCorridor_of_cutMeetsAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : bc_CutMeetsAxis ω x j L) :
    cnp_ClusterMeetsCorridor ω x j L := h









theorem bc_cutMeetsAxis_meets_corridorCell (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} {j : Fin d} {L : ℕ} (h : bc_CutMeetsAxis ω x j L) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ L + 1 ∧
      Connected d (removeSite 0 ω) x (hrHD_rayPt j (m : ℤ)) := h.1


theorem bc_cutMeetsAxis_cluster_infinite (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} {j : Fin d} {L : ℕ} (h : bc_CutMeetsAxis ω x j L) :
    (cluster d (removeSite 0 ω) x).Infinite := h.2




theorem bc_cutMeetsAxis_witness_ne_zero (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} {j : Fin d} {L : ℕ} (h : bc_CutMeetsAxis ω x j L) :
    x ≠ 0 :=
  bkm_witness_ne_zero ω h.2












theorem bc_cutMeetsAxis_corridorCell (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j (m : ℤ))).Infinite) :
    bc_CutMeetsAxis ω (hrHD_rayPt j (m : ℤ)) j L :=
  ⟨⟨m, hm1, hmL, connected_rfl⟩, hinf⟩






theorem bc_cutMeetsAxis_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    bc_CutMeetsAxis ω (hrHD_rayPt j 1) j L := by
  have h := bc_cutMeetsAxis_corridorCell ω j L 1 le_rfl (by omega) (by simpa using hinf)
  simpa using h













theorem bc_cut_someAxis_reach_of_infinite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y :=
  cnp_cut_someAxis_reach_of_infinite ω x hinf n














theorem bc_axisRoutingPremise_of_cutMeetsAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : bc_CutMeetsAxis ω x j L) :
    craf_AxisRoutingPremise ω x j L :=
  cnp_axisRoutingPremise_of_clusterMeetsCorridor ω x j L h





theorem bc_axisAssignment_of_cutMeetsAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : bc_CutMeetsAxis ω x j L) :
    crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  cnp_axisAssignment_of_clusterMeetsCorridor ω x j L h







theorem bc_clusterReachesRay_of_cutMeetsAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : bc_CutMeetsAxis ω x j L) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  cnp_clusterReachesRay_of_clusterMeetsCorridor ω x j L h




















theorem bc_cut_meets_axis (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) :
    ((cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite →
        bc_CutMeetsAxis ω (hrHD_rayPt j 1) j L) ∧
      (∀ x : Site d, bc_CutMeetsAxis ω x j L →
        craf_AxisRoutingPremise ω x j L ∧ x ≠ 0) :=
  ⟨fun hinf => bc_cutMeetsAxis_neighbour ω j L hinf,
    fun x h => ⟨bc_axisRoutingPremise_of_cutMeetsAxis ω x j L h,
      bc_cutMeetsAxis_witness_ne_zero ω h⟩⟩

end Walls

end StatMech
