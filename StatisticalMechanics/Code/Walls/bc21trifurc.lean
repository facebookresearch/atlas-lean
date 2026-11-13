/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Code.Walls.bc20mengerroute
import Code.Walls.bc12core
import Code.Percolation.CanonicalTrifCount

open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech.Walls

variable {d : ℕ}





























theorem bc21_mengerCore_of_canonicalTrifurcation (ω : ConfigSpace (Sym2 (Site d)))
    (htri : IsCanonicalTrifurcation d ω 0) : MengerCore ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := htri
  exact mng_mengerCore_of_neighborClusters ω a₁ a₂ a₃ hne
    ⟨hadj.1.1, hadj.2.1.1, hadj.2.2.1⟩ hinf
    ⟨bc12_cluster_ne_of_not_connected hsep.1,
      bc12_cluster_ne_of_not_connected hsep.2.1,
      bc12_cluster_ne_of_not_connected hsep.2.2⟩
















def bc21_OriginBranchSurvivalCut (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    ((cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite) ∧
    (¬ Connected d (removeSite 0 ω) a₁ a₂ ∧
      ¬ Connected d (removeSite 0 ω) a₁ a₃ ∧
      ¬ Connected d (removeSite 0 ω) a₂ a₃)




theorem bc21_mengerCore_of_originBranchSurvivalCut (ω : ConfigSpace (Sym2 (Site d)))
    (h : bc21_OriginBranchSurvivalCut d ω) : MengerCore ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := h
  exact mng_mengerCore_of_neighborClusters ω a₁ a₂ a₃ hne hadj hinf
    ⟨bc12_cluster_ne_of_not_connected hsep.1,
      bc12_cluster_ne_of_not_connected hsep.2.1,
      bc12_cluster_ne_of_not_connected hsep.2.2⟩





theorem bc21_originBranchSurvivalCut_of_canonicalTrifurcation
    (ω : ConfigSpace (Sym2 (Site d))) (htri : IsCanonicalTrifurcation d ω 0) :
    bc21_OriginBranchSurvivalCut d ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := htri
  exact ⟨a₁, a₂, a₃, hne, ⟨hadj.1.1, hadj.2.1.1, hadj.2.2.1⟩, hinf, hsep⟩











theorem bc21_arm_infinite_removeOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (htri : IsCanonicalTrifurcation d ω 0) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃) ∧
      (∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) a₁ y) ∧
      (∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) a₂ y) ∧
      (∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) a₃ y) := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, _⟩ := htri
  exact ⟨a₁, a₂, a₃, hne, ⟨hadj.1.1, hadj.2.1.1, hadj.2.2.1⟩,
    (cluster_infinite_iff (removeSite 0 ω) a₁).mp hinf.1,
    (cluster_infinite_iff (removeSite 0 ω) a₂).mp hinf.2.1,
    (cluster_infinite_iff (removeSite 0 ω) a₃).mp hinf.2.2⟩














theorem bc21_mengerRoutingCover_of_boxTrifurcation (n : ℕ)
    (h : bc12_BoxOriginTrifurcation d n) : MengerRoutingCover d n :=
  fun ω hω => bc21_mengerCore_of_canonicalTrifurcation ω (h ω hω)











theorem bc21_burtonKeane_uniqueness_of_boxTrifurcation
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hr : ∀ n : ℕ, bc12_BoxOriginTrifurcation d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  mng_burton_keane_uniqueness_mengerCover μ herg hfe bdry hbound hvol hdens
    (fun n => bc21_mengerRoutingCover_of_boxTrifurcation n (hr n))








open StatMech.Percolation.CtcWitness in

theorem bc21_px0_eq_origin : px 0 = (0 : Site 2) := by
  funext i; fin_cases i <;> simp [px]

open StatMech.Percolation.CtcWitness in




theorem bc21_threeRay_trif_at_origin :
    IsCanonicalTrifurcation 2 threeRayConfig 0 := by
  classical
  rw [← bc21_px0_eq_origin]
  refine ⟨px 1, py 1, px (-1), ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro hh
      have hc : (px 1) 1 = (py 1) 1 := by rw [hh]
      simp [px, py] at hc
    · intro hh
      have h0 : (1 : ℤ) = -1 := px_inj hh
      omega
    · intro hh
      have hc : (py 1) 0 = (px (-1)) 0 := by rw [hh]
      simp [px, py] at hc
  · refine ⟨⟨px_adj 0, ?_⟩, ⟨py_adj 0, ?_⟩, ?_, ?_⟩
    · have := px_ray_open 0; simpa [px] using this
    · have := py_ray_open 0 (le_refl 0); simpa [py] using this
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [px]
    · have := px_ray_open (-1)
      rw [show ((-1 : ℤ) + 1) = 0 by ring] at this
      rw [Sym2.eq_swap]; simpa [px] using this
  · exact ⟨cut_px_pos_infinite, cut_py_pos_infinite, cut_px_neg_infinite⟩
  · exact ⟨cut_disconnect_pos_py, cut_disconnect_pos_neg, fun hh =>
      cut_disconnect_neg_py hh.symm⟩




theorem bc21_originBranchSurvivalCut_nonvacuous :
    ∃ ω : ConfigSpace (Sym2 (Site 2)), bc21_OriginBranchSurvivalCut 2 ω :=
  ⟨StatMech.Percolation.CtcWitness.threeRayConfig,
    bc21_originBranchSurvivalCut_of_canonicalTrifurcation _ bc21_threeRay_trif_at_origin⟩




theorem bc21_mengerCore_nonvacuous :
    ∃ ω : ConfigSpace (Sym2 (Site 2)), MengerCore ω :=
  ⟨StatMech.Percolation.CtcWitness.threeRayConfig,
    bc21_mengerCore_of_canonicalTrifurcation _ bc21_threeRay_trif_at_origin⟩



section AxiomAudit


#guard_msgs in
#print axioms bc21_mengerCore_of_canonicalTrifurcation


#guard_msgs in
#print axioms bc21_mengerCore_of_originBranchSurvivalCut


#guard_msgs(whitespace := lax) in
#print axioms bc21_originBranchSurvivalCut_of_canonicalTrifurcation


#guard_msgs in
#print axioms bc21_arm_infinite_removeOrigin


#guard_msgs in
#print axioms bc21_mengerRoutingCover_of_boxTrifurcation


#guard_msgs(whitespace := lax) in
#print axioms bc21_burtonKeane_uniqueness_of_boxTrifurcation


#guard_msgs in
#print axioms bc21_threeRay_trif_at_origin


#guard_msgs in
#print axioms bc21_originBranchSurvivalCut_nonvacuous

end AxiomAudit

end StatMech.Walls
