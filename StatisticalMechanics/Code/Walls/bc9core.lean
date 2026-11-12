/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Walls.bc8core
import Code.Walls.bc9nbrcutcluster
import Code.Walls.bc9cutsurvives
import Code.Walls.bc9distinctcutclusters

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory

namespace StatMech

namespace Walls

variable {d : ℕ}



























def bc9_BoxOriginReach (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    ∃ y₁ y₂ y₃ : Site d,
      y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧
      Connected d (forceOpenFinset W ω) 0 y₁ ∧
      Connected d (forceOpenFinset W ω) 0 y₂ ∧
      Connected d (forceOpenFinset W ω) 0 y₃ ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) y₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) y₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) y₃).Infinite ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₃





















theorem bc9_originRewiring_of_boxOriginReach (n : ℕ) (h : bc9_BoxOriginReach d n) :
    bc8_OriginRewiring d n := by
  intro ω hω
  obtain ⟨W, hW0, y₁, y₂, y₃, hy1, hy2, hy3, hc1, hc2, hc3,
    hi1, hi2, hi3, hd12, hd13, hd23⟩ := h ω hω
  
  obtain ⟨n₁, hadj1, hconn1, _hmem1⟩ :=
    bc9nbr_mem_neighbour_cutCluster_strong (forceOpenFinset W ω) hy1 hc1
  obtain ⟨n₂, hadj2, hconn2, _hmem2⟩ :=
    bc9nbr_mem_neighbour_cutCluster_strong (forceOpenFinset W ω) hy2 hc2
  obtain ⟨n₃, hadj3, hconn3, _hmem3⟩ :=
    bc9nbr_mem_neighbour_cutCluster_strong (forceOpenFinset W ω) hy3 hc3
  
  have e1 : cluster d (removeSite 0 (forceOpenFinset W ω)) n₁
      = cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ := cluster_eq_of_connected hconn1
  have e2 : cluster d (removeSite 0 (forceOpenFinset W ω)) n₂
      = cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ := cluster_eq_of_connected hconn2
  have e3 : cluster d (removeSite 0 (forceOpenFinset W ω)) n₃
      = cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ := cluster_eq_of_connected hconn3
  refine ⟨W, hW0, n₁, n₂, n₃, hadj1, hadj2, hadj3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact hi1
  · rw [e2]; exact hi2
  · rw [e3]; exact hi3
  · rw [e1, e2]; exact hd12
  · rw [e1, e3]; exact hd13
  · rw [e2, e3]; exact hd23










theorem bc9_canonicalTrif_of_boxOriginReach (n : ℕ) (h : bc9_BoxOriginReach d n)
    (ω : ConfigSpace (Sym2 (Site d))) (hω : ω ∈ threeMeetBox d n) :
    ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 :=
  bc8_canonicalTrif_of_originRewiring n (bc9_originRewiring_of_boxOriginReach n h) ω hω










theorem bc9_burtonKeane_uniqueness_of_boxOriginReach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hr : ∀ n : ℕ, bc9_BoxOriginReach d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc8_burtonKeane_uniqueness_of_originRewiring μ herg hfe bdry hbound hvol hdens
    (fun n => bc9_originRewiring_of_boxOriginReach n (hr n))









theorem bc9_forceOpenFinset_empty (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
  funext e; simp [forceOpenFinset]






theorem bc9_boxOriginReach_of_reach (ω : ConfigSpace (Sym2 (Site d)))
    {y₁ y₂ y₃ : Site d} (hy1 : y₁ ≠ 0) (hy2 : y₂ ≠ 0) (hy3 : y₃ ≠ 0)
    (hc1 : Connected d ω 0 y₁) (hc2 : Connected d ω 0 y₂) (hc3 : Connected d ω 0 y₃)
    (hi1 : (cluster d (removeSite 0 ω) y₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) y₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) y₃).Infinite)
    (hd12 : cluster d (removeSite 0 ω) y₁ ≠ cluster d (removeSite 0 ω) y₂)
    (hd13 : cluster d (removeSite 0 ω) y₁ ≠ cluster d (removeSite 0 ω) y₃)
    (hd23 : cluster d (removeSite 0 ω) y₂ ≠ cluster d (removeSite 0 ω) y₃) :
    ∃ W : Finset (Sym2 (Site d)),
      (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      ∃ z₁ z₂ z₃ : Site d,
        z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ z₃ ≠ 0 ∧
        Connected d (forceOpenFinset W ω) 0 z₁ ∧
        Connected d (forceOpenFinset W ω) 0 z₂ ∧
        Connected d (forceOpenFinset W ω) 0 z₃ ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) z₁).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) z₂).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) z₃).Infinite ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) z₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) z₂ ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) z₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) z₃ ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) z₂ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) z₃ := by
  refine ⟨∅, by simp, y₁, y₂, y₃, hy1, hy2, hy3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [bc9_forceOpenFinset_empty]
  · exact hc1
  · exact hc2
  · exact hc3
  · exact hi1
  · exact hi2
  · exact hi3
  · exact hd12
  · exact hd13
  · exact hd23




















theorem bc9_originRewiring_iff_residue (n : ℕ) :
    bc9_BoxOriginReach d n → bc8_OriginRewiring d n :=
  bc9_originRewiring_of_boxOriginReach n



section AxiomAudit


#guard_msgs in
#print axioms bc9_originRewiring_of_boxOriginReach


#guard_msgs in
#print axioms bc9_canonicalTrif_of_boxOriginReach


#guard_msgs in
#print axioms bc9_burtonKeane_uniqueness_of_boxOriginReach


#guard_msgs in
#print axioms bc9_boxOriginReach_of_reach

end AxiomAudit

end Walls

end StatMech
