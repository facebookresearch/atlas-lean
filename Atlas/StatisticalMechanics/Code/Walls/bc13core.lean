/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































































import Mathlib
import Code.Percolation.TrifurcationConstruction
import Code.Percolation.HrouteHighDim
import Code.Percolation.TrifurcationExistence2
import Code.Percolation.LatticeMengerAttach
import Code.Percolation.ClusterRunsAxisFE

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}



















def bc13_BoxClusterReachesRay (d n : ℕ) : Prop :=
  lma_BoxClusterReachesRay d n


























theorem bc13_hroute_of_clusterReachesRay
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hreach : ∀ n : ℕ, bc13_BoxClusterReachesRay d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  hrHD_route_of_routing μ hfe
    (fun n => tex_disjointRouting_of_box (lma_boxAttachData_of_reachesRay (hreach n)))





theorem bc13_htrif_of_clusterReachesRay
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hreach : ∀ n : ℕ, bc13_BoxClusterReachesRay d n) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0} :=
  htrif_discharged μ hfe (bc13_hroute_of_clusterReachesRay μ hfe hreach)













theorem bc13_burton_keane_uniqueness_of_clusterReachesRay
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hreach : ∀ n : ℕ, bc13_BoxClusterReachesRay d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_trif_route μ herg hfe bdry hbound hvol hdens
    (bc13_hroute_of_clusterReachesRay μ hfe hreach)





















theorem bc13_clusterReachesRay_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay ω (hrHD_rayPt j 1) j := by
  refine ⟨0, self_mem_cluster ω (hrHD_rayPt j 1), ?_, ?_, hinf⟩
  · 
    intro e he
    rw [lma_corridorEdges_zero] at he
    exact absurd he (Finset.notMem_empty e)
  · 
    have h1 : hrHD_rayPt j (((0 : ℕ) : ℤ) + 1) = hrHD_rayPt j 1 := by norm_num
    rw [h1]












theorem bc13_boxClusterReachesRay_nonvacuous (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hx1 : x₁ = hrHD_rayPt j₁ 1) (hx2 : x₂ = hrHD_rayPt j₂ 1) (hx3 : x₃ = hrHD_rayPt j₃ 1)
    (hi1 : (cluster d (removeSite 0 ω) x₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) x₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) x₃).Infinite) :
    ∃ j₁' j₂' j₃' : Fin d,
      lma_ClusterReachesRay ω x₁ j₁' ∧ lma_ClusterReachesRay ω x₂ j₂' ∧
        lma_ClusterReachesRay ω x₃ j₃' := by
  subst hx1 hx2 hx3
  exact ⟨j₁, j₂, j₃,
    bc13_clusterReachesRay_neighbour ω j₁ hi1,
    bc13_clusterReachesRay_neighbour ω j₂ hi2,
    bc13_clusterReachesRay_neighbour ω j₃ hi3⟩



















theorem bc13_clusterReachesRay_arbitrary_omega_record (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (hinf : (cluster d ω x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y :=
  craf_someAxis_reach_of_infinite ω x hinf n



section AxiomAudit


#guard_msgs(whitespace := lax) in
#print axioms bc13_hroute_of_clusterReachesRay


#guard_msgs(whitespace := lax) in
#print axioms bc13_htrif_of_clusterReachesRay


#guard_msgs(whitespace := lax) in
#print axioms bc13_burton_keane_uniqueness_of_clusterReachesRay


#guard_msgs(whitespace := lax) in
#print axioms bc13_clusterReachesRay_neighbour


#guard_msgs(whitespace := lax) in
#print axioms bc13_boxClusterReachesRay_nonvacuous


#guard_msgs(whitespace := lax) in
#print axioms bc13_clusterReachesRay_arbitrary_omega_record

end AxiomAudit

end Walls

end StatMech
