/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Percolation.ClusterRunsAxisFE
import Code.Percolation.MengerCorridors
import Code.Percolation.LatticeMengerAttach
import Code.Percolation.HrouteHighDim
import Code.Probability.MengerSplice

open MeasureTheory Set SimpleGraph
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Combinatorics

namespace StatMech

namespace Percolation

variable {d : ℕ}












theorem cnp_mouth_connected_corridorCell (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1) :
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) :=
  mco_corridorVert_connected ω j (L + 1) m hm1 hmL








theorem cnp_removeSite_le (ω : ConfigSpace (Sym2 (Site d))) (z : Site d) :
    removeSite z ω ≤ ω := by
  intro e
  by_cases h : z ∈ e
  · rw [removeSite_apply_of_mem h]; exact bot_le
  · rw [removeSite_apply_of_notMem h]





















def cnp_ClusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (L : ℕ) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ m ≤ L + 1 ∧
    Connected d (removeSite 0 ω) x (hrHD_rayPt j (m : ℤ))) ∧
  (cluster d (removeSite 0 ω) x).Infinite
























theorem cnp_axisRoutingPremise_of_clusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d)))
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















theorem cnp_mouth_attachment_isPath (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (x : Site d) (m : ℕ)
    (pA : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk
      x (hrHD_rayPt j (m : ℤ)))
    (pB : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk
      (hrHD_rayPt j (m : ℤ)) (hrHD_rayPt j 1))
    (hpA : pA.IsPath) (hpB : pB.IsPath)
    (hmeet : ∀ z, z ∈ pA.support → z ∈ pB.support → z = hrHD_rayPt j (m : ℤ)) :
    (pA.append pB).IsPath :=
  mgs_append_isPath hpA hpB hmeet







theorem cnp_exists_simplePath_mouth (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
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














theorem cnp_clusterReachesRay_of_clusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : cnp_ClusterMeetsCorridor ω x j L) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  craf_clusterReachesRay_of_insertion ω x j L
    (cnp_axisRoutingPremise_of_clusterMeetsCorridor ω x j L h)





theorem cnp_axisAssignment_of_clusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : cnp_ClusterMeetsCorridor ω x j L) :
    crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  craf_axisAssignment_of_insertion ω x j L
    (cnp_axisRoutingPremise_of_clusterMeetsCorridor ω x j L h)




















theorem cnp_burton_keane_uniqueness_of_boxReachesRay
    (hd : 3 ≤ d)
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hres : ∀ n : ℕ, lma_BoxClusterReachesRay d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  (hrHD_burton_keane_uniqueness_dim_ge_three hd μ herg hfe bdry hbound hvol hdens
    (fun n => lma_disjointRouting_of_reachesRay (hres n))).2















theorem cnp_clusterMeetsCorridor_corridorCell (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j (m : ℤ))).Infinite) :
    cnp_ClusterMeetsCorridor ω (hrHD_rayPt j (m : ℤ)) j L :=
  ⟨⟨m, hm1, hmL, connected_rfl⟩, hinf⟩






theorem cnp_axisRoutingPremise_corridorCell (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j (m : ℤ))).Infinite) :
    craf_AxisRoutingPremise ω (hrHD_rayPt j (m : ℤ)) j L :=
  cnp_axisRoutingPremise_of_clusterMeetsCorridor ω (hrHD_rayPt j (m : ℤ)) j L
    (cnp_clusterMeetsCorridor_corridorCell ω j L m hm1 hmL hinf)





theorem cnp_clusterMeetsCorridor_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    cnp_ClusterMeetsCorridor ω (hrHD_rayPt j 1) j L := by
  have h := cnp_clusterMeetsCorridor_corridorCell ω j L 1 le_rfl (by omega) (by
    simpa using hinf)
  simpa using h















theorem cnp_cut_someAxis_reach_of_infinite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y :=
  crr_infinite_reaches_far_coord (removeSite 0 ω) x hinf n

end Percolation

end StatMech
