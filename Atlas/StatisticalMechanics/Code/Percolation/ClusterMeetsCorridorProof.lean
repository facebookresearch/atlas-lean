/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Mathlib
import Code.Percolation.ClusterReachesRay
import Code.Percolation.CorridorConnectProof
import Code.Percolation.AxisAssignmentClose

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}
























theorem cmc_clusterMeetsCorridor_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : crr_ClusterRunsAlongAxis ω x j) :
    cnp_ClusterMeetsCorridor ω x j L := by
  obtain ⟨L', _, _, hcut, hinf⟩ := h
  refine ⟨⟨1, le_rfl, by omega, ?_⟩, hinf⟩
  simpa using hcut












theorem cmc_axisRoutingPremise_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : crr_ClusterRunsAlongAxis ω x j) :
    craf_AxisRoutingPremise ω x j L :=
  cnp_axisRoutingPremise_of_clusterMeetsCorridor ω x j L
    (cmc_clusterMeetsCorridor_of_runsAlongAxis ω x j L h)





theorem cmc_clusterReachesRay_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (L : ℕ) (h : crr_ClusterRunsAlongAxis ω x j) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  cnp_clusterReachesRay_of_clusterMeetsCorridor ω x j L
    (cmc_clusterMeetsCorridor_of_runsAlongAxis ω x j L h)

















theorem cmc_runsAlongAxis_entails_uncut_connection (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    Connected d ω x (hrHD_rayPt j 1) := by
  obtain ⟨_, _, huncut, _, _⟩ := h
  exact huncut













theorem cmc_clusterMeetsCorridor_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ) (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    cnp_ClusterMeetsCorridor ω (hrHD_rayPt j 1) j L :=
  cmc_clusterMeetsCorridor_of_runsAlongAxis ω (hrHD_rayPt j 1) j L
    (crr_runsAlongAxis_of_neighbour ω j hinf)

























theorem cmc_burton_keane_uniqueness_of_boxCandidates
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
  cnp_burton_keane_uniqueness_of_boxReachesRay hd μ herg hfe bdry hbound hvol hdens
    (fun n => caa_boxClusterReachesRay (hcand n))







theorem cmc_candidates_nonvacuous (ω : ConfigSpace (Sym2 (Site d)))
    (a : Fin 3 → Fin d) (ha : Function.Injective a)
    (hinf : ∀ i : Fin 3, (cluster d (removeSite 0 ω) (hrHD_rayPt (a i) 1)).Infinite) :
    caa_RunsAlongCandidates ω (fun i => hrHD_rayPt (a i) 1)
      (fun i => ({a i} : Finset (Fin d))) :=
  caa_candidates_neighbour_witnesses ω a ha hinf

end Percolation

end StatMech
