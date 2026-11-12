/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Percolation.ClusterRunsAxisFE
import Code.Percolation.ClusterMeetsCorridorProof
import Code.Percolation.AxisAssignmentClose

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}



















theorem rap_runsAlongAxis_ray_open_edges (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    {t : ℕ} (ht : t < L) :
    forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω
      s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true :=
  craf_corridor_axis_edge_open ω j L ht

















theorem rap_runsAlongAxis_ray (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    (∀ t : ℕ, t < L → forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω
        s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true) ∧
      crr_ClusterRunsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
        (hrHD_rayPt j 1) j := by
  refine ⟨fun t ht => rap_runsAlongAxis_ray_open_edges ω j L ht, ?_⟩
  exact craf_clusterRunsAlongAxis_of_insertion ω (hrHD_rayPt j 1) j L
    (craf_axisRoutingPremise_neighbour ω j L hinf)








theorem rap_far_reach (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) :
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) :=
  crr_axisOpen_connected_removeSite (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) j L
    (fun _t ht => rap_runsAlongAxis_ray_open_edges ω j L ht) L le_rfl







theorem rap_clusterReachesRay_ray (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
      (hrHD_rayPt j 1) j :=
  crr_clusterReachesRay_of_runsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
    (hrHD_rayPt j 1) j (rap_runsAlongAxis_ray ω j L hinf).2














theorem rap_clusterMeetsCorridor_ray (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L L' : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    cnp_ClusterMeetsCorridor (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
      (hrHD_rayPt j 1) j L' :=
  cmc_clusterMeetsCorridor_of_runsAlongAxis
    (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j L'
    (rap_runsAlongAxis_ray ω j L hinf).2

























theorem rap_burton_keane_uniqueness
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
    (hcand : ∀ n : ℕ, caa_BoxRunsAlongCandidates d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  cmc_burton_keane_uniqueness_of_boxCandidates hd μ herg hfe bdry hbound hvol hdens hcand













theorem rap_ray_open_edge_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hL : 1 ≤ L) :
    forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω
      s(hrHD_rayPt j (((0 : ℕ) : ℤ) + 1), hrHD_rayPt j (((0 : ℕ) : ℤ) + 2)) = true :=
  rap_runsAlongAxis_ray_open_edges ω j L (t := 0) (by omega)








theorem rap_candidates_neighbour (ω : ConfigSpace (Sym2 (Site d)))
    (a : Fin 3 → Fin d) (ha : Function.Injective a)
    (hinf : ∀ i : Fin 3, (cluster d (removeSite 0 ω) (hrHD_rayPt (a i) 1)).Infinite) :
    caa_RunsAlongCandidates ω (fun i => hrHD_rayPt (a i) 1)
      (fun i => ({a i} : Finset (Fin d))) :=
  caa_candidates_neighbour_witnesses ω a ha hinf


















theorem rap_runsAlongAxis_entails_near_connection (ω : ConfigSpace (Sym2 (Site d)))
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
