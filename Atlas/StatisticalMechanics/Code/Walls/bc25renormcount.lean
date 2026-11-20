/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Walls.bc24coarsetrif
import Code.Percolation.ArmEndDisjointClose
import Code.Percolation.BKForestLib
import Code.Percolation.BurtonKeaneErgodic
import Code.Percolation.BurtonKeaneClose

open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal Topology
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}














theorem bc25_isTrifurcation_of_coarseTrif_zero {ω : ConfigSpace (Sym2 (Site d))}
    (h : IsCoarseTrifurcation d 0 ω) : IsTrifurcation d ω (0 : Site d) := by
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hne, hbox, _hadj, hconn, hinf, hsep⟩ := h
  
  have hbox0 : ∀ {b : Site d}, b ∈ box d 0 → b = (0 : Site d) := by
    intro b hb; rw [bc24_box_zero] at hb; simpa using hb
  have hb₁0 : b₁ = (0 : Site d) := hbox0 hbox.1
  have hb₂0 : b₂ = (0 : Site d) := hbox0 hbox.2.1
  have hb₃0 : b₃ = (0 : Site d) := hbox0 hbox.2.2
  
  have hbridge := bc24_removeSites_box_zero (d := d) ω
  
  rw [hbridge] at hinf hsep
  refine ⟨a₁, a₂, a₃, hne, ?_, ?_, ?_⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · exact (hb₁0 ▸ hconn.1).symm
    · exact (hb₂0 ▸ hconn.2.1).symm
    · exact (hb₃0 ▸ hconn.2.2).symm
  · 
    exact ⟨hinf.1.mono (ctc2_cluster_removeSite_subset 0 a₁ ω),
      hinf.2.1.mono (ctc2_cluster_removeSite_subset 0 a₂ ω),
      hinf.2.2.mono (ctc2_cluster_removeSite_subset 0 a₃ ω)⟩
  · 
    exact hsep








theorem bc25_coarseTrif_zero_chain {ω : ConfigSpace (Sym2 (Site d))} :
    (IsCanonicalTrifurcation d ω (0 : Site d) → IsCoarseTrifurcation d 0 ω) ∧
      (IsCoarseTrifurcation d 0 ω → IsTrifurcation d ω (0 : Site d)) :=
  ⟨bc24_coarseTrif_of_canonical_origin, bc25_isTrifurcation_of_coarseTrif_zero⟩







theorem bc25_bridge_nonvacuous :
    ∃ ω : ConfigSpace (Sym2 (Site 2)),
      IsCoarseTrifurcation 2 0 ω ∧ IsTrifurcation 2 ω (0 : Site 2) := by
  obtain ⟨ω, hω⟩ := bc24_coarseTrif_nonvacuous
  exact ⟨ω, hω, bc25_isTrifurcation_of_coarseTrif_zero hω⟩
















theorem bc25_Tcount_le_boundary_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : aed_GlobalForestArms ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  aed_Tcount_le_boundary_of_globalForestArms ω n hn h





theorem bc25_Tcount_le_boundary_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bkfl_ForestPeel ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bkfl_Tcount_le_boundary_of_forestPeel ω n hn h






theorem bc25_Tcount_zero_le_box (ω : ConfigSpace (Sym2 (Site d))) :
    Tcount d ω 0 ≤ (boxFinsetBK d 0).card := by
  classical
  unfold Tcount
  exact Finset.card_filter_le _ _
















theorem bc25_burton_keane_uniqueness_of_forest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
    (hdens : Filter.Tendsto
      (fun n => (boxSV_boundaryCard d n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0})
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    ∃ k : ℕ∞, k ≤ 1 ∧ μ {ω | numInfiniteClusters d ω = k} = 1
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  classical
  
  
  
  
  refine burton_keane_uniqueness μ herg
    (fun n => if 1 ≤ n then boxSV_boundaryCard d n else (boxFinsetBK d n).card)
    (fun ω n => ?_) (fun n => bkc_boxFinsetBK_card_pos d n) ?_ htrif hmerge
  · by_cases hn : 1 ≤ n
    · simp only [hn, if_true]
      exact bc25_Tcount_le_boundary_of_globalForestArms ω n hn (hres ω n hn)
    · simp only [hn, if_false]
      have hn0 : n = 0 := by omega
      subst hn0
      exact bc25_Tcount_zero_le_box ω
  · 
    
    refine hdens.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simp only [hn, if_true]








theorem bc25_burton_keane_bernoulli_of_forest (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  aed_burton_keane_bernoulli_of_globalForestArms hd p hp1 hp0 hres htrif

end StatMech.Walls
