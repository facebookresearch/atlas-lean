/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Code.FK.FKUniqPerEdge
import Code.FK.RotationInvariance
import Code.FK.BulkDeviationProof
import Code.FK.UniformBulkDeviation
import Code.FK.SpatialCollapse

open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}














theorem gec_freeSandwich_of_rotation (hd : 1 ≤ d) (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hres : ocs_FreeRotationResidue (d := d) N e' t) :
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        freeEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t)
          = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧
      (∀ n, ∀ e ∈ In n,
        freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - δ n
          ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0) := by
  refine ⟨ocs_bulkSet d, ocs_freeDelta N e' t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro n e he
    rw [ocs_bulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => ocs_freeDelta_nonneg N e' t n
  · exact ocs_freeDelta_tendsto_zero N e' t hres
  · 
    intro n e he
    rw [ocs_bulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [edgeIncl_innerEdgeLE]
    exact hres (n - Nat.sqrt n) eb heb
  · 
    intro n e he
    rw [ocs_bulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset] at heb
    by_cases hn : 1 ≤ n
    · induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        exact ocs_free_bulk_lower N e' t n hn u v heb
    · 
      exfalso
      have hn0 : n = 0 := by omega
      subst hn0
      induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        have huv : (u : Site d) = (v : Site d) := by
          have hu := u.2; have hv := v.2
          funext i
          have h1 := hu i; have h2 := hv i
          simp only [Nat.zero_sub] at h1 h2; omega
        rw [boxGraph, SimpleGraph.comap_adj] at heb
        change NearestNeighbour d (u : Site d) (v : Site d) at heb
        rw [huv] at heb
        rw [show NearestNeighbour d (v : Site d) (v : Site d)
              ↔ (∑ i, ((v : Site d) i - (v : Site d) i).natAbs) = 1 from Iff.rfl] at heb
        simp at heb
  · 
    have hcard : ∀ n, (ocs_bulkSet d n).card = (boxGraph d (n - Nat.sqrt n)).edgeFinset.card :=
      fun n => Finset.card_image_of_injective _
        (dfi_innerEdgeLE_injective d (Nat.sub_le n (Nat.sqrt n)))
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd (fun n => n - Nat.sqrt n)
      (fun n => Nat.sub_le n _) ocs_gap_sub_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]




theorem gec_wiredSandwich_of_rotation (hd : 1 ≤ d) (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hres : ocs_WiredRotationResidue (d := d) N e' t) :
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        wiredEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t)
          = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧
      (∀ n, ∀ e ∈ In n,
        edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
          ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0) := by
  refine ⟨ocs_wiredBulkSet d, ocs_wiredDelta N e' t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n e he
    rw [ocs_wiredBulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => ocs_wiredDelta_nonneg N e' t n
  · exact ocs_wiredDelta_tendsto_zero N e' t hres
  · 
    intro n e he
    rw [ocs_wiredBulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [edgeIncl_innerEdgeLE]
    exact hres (n - Nat.sqrt n - 1) eb heb
  · 
    intro n e he
    rw [ocs_wiredBulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset] at heb
    by_cases hn : 2 ≤ n
    · induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        exact ocs_wired_bulk_upper N e' t n hn u v heb
    · 
      exfalso
      have hzero : n - Nat.sqrt n - 1 = 0 := by
        have hsq : Nat.sqrt n = 0 ∨ Nat.sqrt n = 1 := by
          interval_cases n <;> simp [Nat.sqrt]
        rcases hsq with h | h <;> rw [h] <;> omega
      induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        have huv : (u : Site d) = (v : Site d) := by
          have hu := u.2; have hv := v.2
          funext i
          have h1 := hu i; have h2 := hv i
          simp only [hzero] at h1 h2; omega
        rw [boxGraph, SimpleGraph.comap_adj] at heb
        change NearestNeighbour d (u : Site d) (v : Site d) at heb
        rw [huv] at heb
        rw [show NearestNeighbour d (v : Site d) (v : Site d)
              ↔ (∑ i, ((v : Site d) i - (v : Site d) i).natAbs) = 1 from Iff.rfl] at heb
        simp at heb
  · 
    have hcard : ∀ n, (ocs_wiredBulkSet d n).card
        = (boxGraph d (n - Nat.sqrt n - 1)).edgeFinset.card :=
      fun n => Finset.card_image_of_injective _ (dfi_innerEdgeLE_injective d _)
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd (fun n => n - Nat.sqrt n - 1)
      (fun n => Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n)))
      ocs_gap_sub_one_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]








theorem gec_freeBulk_of_sandwich (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hsand : ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        freeEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t)
          = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧
      (∀ n, ∀ e ∈ In n,
        freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - δ n
          ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)) :
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e
          - freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0) := by
  obtain ⟨In, δ, hIE, hδ0, hδlim, hhom, hlow, hbdy⟩ := hsand
  refine ⟨In, δ, hIE, hδ0, hδlim, ?_, hbdy⟩
  intro n e he
  set L := freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) with hL
  
  have hup : edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e ≤ L := by
    rw [← hhom n e he]
    exact bdp_free_per_edge_upper n e (fsc_logistic_pos t) (fsc_logistic_lt_one t)
  
  have hlo : L - δ n ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e := hlow n e he
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩


theorem gec_wiredBulk_of_sandwich (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hsand : ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        wiredEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t)
          = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧
      (∀ n, ∀ e ∈ In n,
        edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
          ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)) :
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
          - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0) := by
  obtain ⟨In, δ, hIE, hδ0, hδlim, hhom, hupb, hbdy⟩ := hsand
  refine ⟨In, δ, hIE, hδ0, hδlim, ?_, hbdy⟩
  intro n e he
  set L := wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) with hL
  
  have hlo : L ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e := by
    rw [← hhom n e he]
    exact bdp_wired_per_edge_lower n e (fsc_logistic_pos t) (fsc_logistic_lt_one t)
  
  have hupbb : edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
      ≤ L + δ n := hupb n e he
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩









theorem gec_freeCollapse_of_bulk (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hbulk : ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e
          - freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)) :
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t))) := by
  obtain ⟨In, δ, hIE, hδ0, hδlim, hin, hbdy⟩ := hbulk
  obtain ⟨hL0, hL1⟩ := ubd_freeEdgeDensity_mem_Icc N e' t
  exact spc_growingBox_collapse t hEbox _ hL0 hL1 In hIE δ hδ0 hδlim hin hbdy


theorem gec_wiredCollapse_of_bulk (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hbulk : ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
          - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t))) := by
  obtain ⟨In, δ, hIE, hδ0, hδlim, hin, hbdy⟩ := hbulk
  obtain ⟨hL0, hL1⟩ := ubd_wiredEdgeDensity_mem_Icc N e' t
  exact ubd_growingBox_wiredCollapse t hEbox _ hL0 hL1 In hIE δ hδ0 hδlim hin hbdy















theorem gec_GenuineFreeCollapse (hd : 1 ≤ d) (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card) :
    fpe2_GenuineFreeCollapse (d := d) N := by
  intro e' he' t
  refine gec_freeCollapse_of_bulk N e' t hEbox ?_
  refine gec_freeBulk_of_sandwich N e' t ?_
  exact gec_freeSandwich_of_rotation hd N e' t
    (rot_freeRotationResidue (lt_of_lt_of_le one_pos hd) N e' he' t)






theorem gec_GenuineWiredCollapse (hd : 1 ≤ d) (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card) :
    fpe2_GenuineWiredCollapse (d := d) N := by
  intro e' he' t
  refine gec_wiredCollapse_of_bulk N e' t hEbox ?_
  refine gec_wiredBulk_of_sandwich N e' t ?_
  exact gec_wiredSandwich_of_rotation hd N e' t
    (rot_wiredRotationResidue (lt_of_lt_of_le one_pos hd) N e' he' t)


























theorem gec_fk_uniqueness_of_perVolume (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fpe2_fk_uniqueness_of_perVolume hd N eb heb hEbox hdata
    (gec_GenuineFreeCollapse hd N hEbox)
    (gec_GenuineWiredCollapse hd N hEbox)

end FK

end StatMech
