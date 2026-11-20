/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































































import Mathlib
import Code.Walls.bc14core
import Code.Percolation.ClusterReachesRay
import Code.Percolation.ClusterRunsAxisFE

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}

















def bc15_NearAxisReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) : Prop :=
  Connected d ω x (hrHD_rayPt j 1) ∧
    Connected d (removeSite 0 ω) x (hrHD_rayPt j 1) ∧
    (cluster d (removeSite 0 ω) x).Infinite






theorem bc15_runsAlongAxis_of_nearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc15_NearAxisReach ω x j) :
    crr_ClusterRunsAlongAxis ω x j := by
  obtain ⟨hnear, hnearCut, hinf⟩ := h
  exact ⟨0, fun t ht => absurd ht (by omega), hnear, hnearCut, hinf⟩




theorem bc15_nearReach_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    bc15_NearAxisReach ω x j := by
  obtain ⟨L, _hopen, hnear, hnearCut, hinf⟩ := h
  exact ⟨hnear, hnearCut, hinf⟩






theorem bc15_runsAlong_iff_nearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) :
    crr_ClusterRunsAlongAxis ω x j ↔ bc15_NearAxisReach ω x j :=
  ⟨bc15_nearReach_of_runsAlongAxis ω x j, bc15_runsAlongAxis_of_nearReach ω x j⟩












theorem bc15_connected_of_cut (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (h : Connected d (removeSite 0 ω) x (hrHD_rayPt j 1)) :
    Connected d ω x (hrHD_rayPt j 1) :=
  connected_mono (removeSite_le 0 ω) h











def bc15_CutNearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) : Prop :=
  Connected d (removeSite 0 ω) x (hrHD_rayPt j 1) ∧
    (cluster d (removeSite 0 ω) x).Infinite




theorem bc15_nearReach_of_cutNearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc15_CutNearReach ω x j) :
    bc15_NearAxisReach ω x j := by
  obtain ⟨hcut, hinf⟩ := h
  exact ⟨bc15_connected_of_cut ω x j hcut, hcut, hinf⟩



theorem bc15_cutNearReach_of_nearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc15_NearAxisReach ω x j) :
    bc15_CutNearReach ω x j := by
  obtain ⟨_hω, hcut, hinf⟩ := h
  exact ⟨hcut, hinf⟩






theorem bc15_runsAlong_iff_cutNearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) :
    crr_ClusterRunsAlongAxis ω x j ↔ bc15_CutNearReach ω x j :=
  ⟨fun h => bc15_cutNearReach_of_nearReach ω x j (bc15_nearReach_of_runsAlongAxis ω x j h),
    fun h => bc15_runsAlongAxis_of_nearReach ω x j (bc15_nearReach_of_cutNearReach ω x j h)⟩



theorem bc15_runsAlongAxis_of_cutNearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc15_CutNearReach ω x j) :
    crr_ClusterRunsAlongAxis ω x j :=
  (bc15_runsAlong_iff_cutNearReach ω x j).mpr h

















def bc15_BoxClusterCutNearReach (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x : Site d, x ∈ box d n → (cluster d ω x).Infinite →
      ∃ j : Fin d, bc15_CutNearReach ω x j






theorem bc15_boxClusterRunsAlong_of_cutNearReach {n : ℕ}
    (h : bc15_BoxClusterCutNearReach d n) : bc14_BoxClusterRunsAlongAxis d n := by
  intro ω hω x hx hinf
  obtain ⟨j, hcnr⟩ := h ω hω x hx hinf
  exact ⟨j, bc15_runsAlongAxis_of_cutNearReach ω x j hcnr⟩





theorem bc15_boxClusterReachesRay_of_cutNearReach {n : ℕ}
    (h : bc15_BoxClusterCutNearReach d n) : lma_BoxClusterReachesRay d n :=
  bc14_boxClusterReachesRay_of_runsAlong (bc15_boxClusterRunsAlong_of_cutNearReach h)





theorem bc15_hroute_of_cutNearReach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hreach : ∀ n : ℕ, bc15_BoxClusterCutNearReach d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  bc14_hroute_of_runsAlong μ hfe
    (fun n => bc15_boxClusterRunsAlong_of_cutNearReach (hreach n))







theorem bc15_burton_keane_uniqueness_of_cutNearReach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hreach : ∀ n : ℕ, bc15_BoxClusterCutNearReach d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc14_burton_keane_uniqueness_of_runsAlong μ herg hfe bdry hbound hvol hdens
    (fun n => bc15_boxClusterRunsAlong_of_cutNearReach (hreach n))











theorem bc15_cutNearReach_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    bc15_CutNearReach ω (hrHD_rayPt j 1) j :=
  ⟨connected_rfl, hinf⟩





theorem bc15_runsAlong_neighbour_of_cutNearReach (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    crr_ClusterRunsAlongAxis ω (hrHD_rayPt j 1) j :=
  bc15_runsAlongAxis_of_cutNearReach ω (hrHD_rayPt j 1) j
    (bc15_cutNearReach_neighbour ω j hinf)





theorem bc15_cutNearReach_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    ∃ j' : Fin d, bc15_CutNearReach ω (hrHD_rayPt j 1) j' :=
  ⟨j, bc15_cutNearReach_neighbour ω j hinf⟩















theorem bc15_cutReach_far_record (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y :=
  craf_someAxis_reach_of_infinite (removeSite 0 ω) x hinf n



section AxiomAudit


#guard_msgs(whitespace := lax) in
#print axioms bc15_runsAlong_iff_nearReach


#guard_msgs(whitespace := lax) in
#print axioms bc15_runsAlong_iff_cutNearReach


#guard_msgs(whitespace := lax) in
#print axioms bc15_boxClusterRunsAlong_of_cutNearReach


#guard_msgs(whitespace := lax) in
#print axioms bc15_boxClusterReachesRay_of_cutNearReach


#guard_msgs(whitespace := lax) in
#print axioms bc15_hroute_of_cutNearReach


#guard_msgs(whitespace := lax) in
#print axioms bc15_burton_keane_uniqueness_of_cutNearReach


#guard_msgs(whitespace := lax) in
#print axioms bc15_runsAlong_neighbour_of_cutNearReach


#guard_msgs(whitespace := lax) in
#print axioms bc15_cutReach_far_record

end AxiomAudit

end Walls

end StatMech
