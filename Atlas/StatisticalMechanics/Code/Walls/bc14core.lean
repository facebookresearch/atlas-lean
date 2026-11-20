/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Walls.bc13core
import Code.Percolation.ClusterReachesRay
import Code.Percolation.ClusterRunsAxisFE
import Code.Percolation.BoxMergeFreeMenger

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}












theorem bc14_rayPt_mem_cluster_of_runsAlong (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    hrHD_rayPt j 1 ∈ cluster d ω x := by
  obtain ⟨_, _, hxe1, _, _⟩ := h
  exact hxe1






theorem bc14_axes_distinct (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d} {j k : Fin d}
    (hne : cluster d ω x ≠ cluster d ω y)
    (hx : crr_ClusterRunsAlongAxis ω x j) (hy : crr_ClusterRunsAlongAxis ω y k) :
    j ≠ k := by
  intro hjk
  subst hjk
  have hxmem : hrHD_rayPt j 1 ∈ cluster d ω x := bc14_rayPt_mem_cluster_of_runsAlong ω x j hx
  have hymem : hrHD_rayPt j 1 ∈ cluster d ω y := bc14_rayPt_mem_cluster_of_runsAlong ω y j hy
  have hdisj : Disjoint (cluster d ω x) (cluster d ω y) := bmm_regions_disjoint ω hne
  have hmem : hrHD_rayPt j 1 ∈ cluster d ω x ∩ cluster d ω y := ⟨hxmem, hymem⟩
  rw [Set.disjoint_iff_inter_eq_empty.mp hdisj] at hmem
  exact absurd hmem (Set.notMem_empty _)

















def bc14_BoxClusterRunsAlongAxis (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x : Site d, x ∈ box d n → (cluster d ω x).Infinite →
      ∃ j : Fin d, crr_ClusterRunsAlongAxis ω x j















theorem bc14_boxClusterReachesRay_of_runsAlong {n : ℕ}
    (h : bc14_BoxClusterRunsAlongAxis d n) : lma_BoxClusterReachesRay d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 _hcd12 _hcd13 _hcd23
  obtain ⟨j₁, hr1⟩ := h ω hω x₁ hb1 hi1
  obtain ⟨j₂, hr2⟩ := h ω hω x₂ hb2 hi2
  obtain ⟨j₃, hr3⟩ := h ω hω x₃ hb3 hi3
  exact ⟨j₁, j₂, j₃,
    crr_clusterReachesRay_of_runsAlongAxis ω x₁ j₁ hr1,
    crr_clusterReachesRay_of_runsAlongAxis ω x₂ j₂ hr2,
    crr_clusterReachesRay_of_runsAlongAxis ω x₃ j₃ hr3⟩




theorem bc14_bc13BoxClusterReachesRay_of_runsAlong {n : ℕ}
    (h : bc14_BoxClusterRunsAlongAxis d n) : bc13_BoxClusterReachesRay d n :=
  bc14_boxClusterReachesRay_of_runsAlong h













theorem bc14_hroute_of_runsAlong
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hrun : ∀ n : ℕ, bc14_BoxClusterRunsAlongAxis d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  bc13_hroute_of_clusterReachesRay μ hfe
    (fun n => bc14_bc13BoxClusterReachesRay_of_runsAlong (hrun n))








theorem bc14_burton_keane_uniqueness_of_runsAlong
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hrun : ∀ n : ℕ, bc14_BoxClusterRunsAlongAxis d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc13_burton_keane_uniqueness_of_clusterReachesRay μ herg hfe bdry hbound hvol hdens
    (fun n => bc14_bc13BoxClusterReachesRay_of_runsAlong (hrun n))












theorem bc14_clusterRunsAlongAxis_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    ∃ j' : Fin d, crr_ClusterRunsAlongAxis ω (hrHD_rayPt j 1) j' :=
  ⟨j, crr_runsAlongAxis_of_neighbour ω j hinf⟩






theorem bc14_boxClusterReachesRay_nonvacuous (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hx1 : x₁ = hrHD_rayPt j₁ 1) (hx2 : x₂ = hrHD_rayPt j₂ 1) (hx3 : x₃ = hrHD_rayPt j₃ 1)
    (hi1 : (cluster d (removeSite 0 ω) x₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) x₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) x₃).Infinite) :
    ∃ j₁' j₂' j₃' : Fin d,
      lma_ClusterReachesRay ω x₁ j₁' ∧ lma_ClusterReachesRay ω x₂ j₂' ∧
        lma_ClusterReachesRay ω x₃ j₃' := by
  subst hx1 hx2 hx3
  refine ⟨j₁, j₂, j₃, ?_, ?_, ?_⟩
  · exact crr_clusterReachesRay_of_runsAlongAxis ω _ j₁ (crr_runsAlongAxis_of_neighbour ω j₁ hi1)
  · exact crr_clusterReachesRay_of_runsAlongAxis ω _ j₂ (crr_runsAlongAxis_of_neighbour ω j₂ hi2)
  · exact crr_clusterReachesRay_of_runsAlongAxis ω _ j₃ (crr_runsAlongAxis_of_neighbour ω j₃ hi3)
















theorem bc14_runsAlong_arbitrary_omega_record (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (hinf : (cluster d ω x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y :=
  craf_someAxis_reach_of_infinite ω x hinf n



section AxiomAudit


#guard_msgs(whitespace := lax) in
#print axioms bc14_axes_distinct


#guard_msgs(whitespace := lax) in
#print axioms bc14_boxClusterReachesRay_of_runsAlong


#guard_msgs(whitespace := lax) in
#print axioms bc14_hroute_of_runsAlong


#guard_msgs(whitespace := lax) in
#print axioms bc14_burton_keane_uniqueness_of_runsAlong


#guard_msgs(whitespace := lax) in
#print axioms bc14_boxClusterReachesRay_nonvacuous


#guard_msgs(whitespace := lax) in
#print axioms bc14_runsAlong_arbitrary_omega_record

end AxiomAudit

end Walls

end StatMech
