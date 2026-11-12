/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.ArmReachComponentClose
import Code.Walls.bc47trifarms
import Code.Walls.bc46funnelproof

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}



open Classical in



noncomputable def bc48_classicalTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Finset (Site d) :=
  (boxFinsetBK d n).filter (fun x => bc47_IsClassicalTrifurcation ω x)

theorem bc48_mem_classicalTrifFinset {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x : Site d} :
    x ∈ bc48_classicalTrifFinset ω n ↔ x ∈ box d n ∧ bc47_IsClassicalTrifurcation ω x := by
  classical
  rw [bc48_classicalTrifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]

open Classical in

noncomputable def bc48_Tcount_classical (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : ℕ :=
  (bc48_classicalTrifFinset ω n).card

theorem bc48_Tcount_classical_eq (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc48_Tcount_classical d ω n = (bc48_classicalTrifFinset ω n).card := rfl



theorem bc48_classicalTrifFinset_subset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc48_classicalTrifFinset ω n ⊆ tfc_trifFinset ω n := by
  intro x hx
  rw [bc48_mem_classicalTrifFinset] at hx
  rw [tfc_mem_trifFinset]
  exact ⟨hx.1, bc47_isTrifurcation_of_classical ω x hx.2⟩





theorem bc48_Tcount_classical_le_Tcount (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc48_Tcount_classical d ω n ≤ Tcount d ω n := by
  rw [bc48_Tcount_classical_eq, ← tfc_trifFinset_card]
  exact Finset.card_le_card (bc48_classicalTrifFinset_subset ω n)













theorem bc48_classical_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x : Site d) (hxbox : x ∈ box d n) (hcl : bc47_IsClassicalTrifurcation ω x) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
      (¬ Connected d (removeSite x ω) a₁ a₂ ∧
       ¬ Connected d (removeSite x ω) a₁ a₃ ∧
       ¬ Connected d (removeSite x ω) a₂ a₃) ∧
      (∃ z₁ ∈ vertexBoundary d (n + 1), Connected d (removeSite x ω) a₁ z₁) ∧
      (∃ z₂ ∈ vertexBoundary d (n + 1), Connected d (removeSite x ω) a₂ z₂) ∧
      (∃ z₃ ∈ vertexBoundary d (n + 1), Connected d (removeSite x ω) a₃ z₃) := by
  obtain ⟨a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, ⟨hi1, hi2, hi3⟩, hsep⟩ := hcl
  
  have hadj1 : (openSubgraph d ω).Adj x a₁ := he1
  have hadj2 : (openSubgraph d ω).Adj x a₂ := he2
  have hadj3 : (openSubgraph d ω).Adj x a₃ := he3
  
  have hb1 : a₁ ∈ box d (n + 1) := arc_neighbour_in_box_succ hxbox he1.1
  have hb2 : a₂ ∈ box d (n + 1) := arc_neighbour_in_box_succ hxbox he2.1
  have hb3 : a₃ ∈ box d (n + 1) := arc_neighbour_in_box_succ hxbox he3.1
  
  have hax1 : a₁ ≠ x := (he1.1.ne).symm
  have hax2 : a₂ ≠ x := (he2.1.ne).symm
  have hax3 : a₃ ≠ x := (he3.1.ne).symm
  
  obtain ⟨z₁, hz1b, hz1c⟩ :=
    arc_connected_removeSite_reaches_boundary ω (n + 1) (by omega) x a₁ hax1 hb1 hi1
  obtain ⟨z₂, hz2b, hz2c⟩ :=
    arc_connected_removeSite_reaches_boundary ω (n + 1) (by omega) x a₂ hax2 hb2 hi2
  obtain ⟨z₃, hz3b, hz3c⟩ :=
    arc_connected_removeSite_reaches_boundary ω (n + 1) (by omega) x a₃ hax3 hb3 hi3
  exact ⟨a₁, a₂, a₃, hne, ⟨hadj1, hadj2, hadj3⟩, hsep,
    ⟨z₁, hz1b, hz1c⟩, ⟨z₂, hz2b, hz2c⟩, ⟨z₃, hz3b, hz3c⟩⟩
















def bc48_ClassicalBoundaryArmInjection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ φ : Site d → Site d,
    (∀ x, x ∈ box d n → bc47_IsClassicalTrifurcation ω x → φ x ∈ vertexBoundary d n) ∧
    (∀ x, x ∈ box d n → bc47_IsClassicalTrifurcation ω x → ∀ y, y ∈ box d n →
      bc47_IsClassicalTrifurcation ω y → φ x = φ y → x = y)




theorem bc48_Tcount_classical_le_boundary_of_residue (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc48_ClassicalBoundaryArmInjection ω n) :
    bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n := by
  classical
  obtain ⟨φ, hmaps, hinj⟩ := h
  rw [bc48_Tcount_classical_eq, ← tfc_boundaryFinset_card]
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, bc48_mem_classicalTrifFinset] at hx
    rw [Finset.mem_coe, tfc_mem_boundaryFinset]
    exact hmaps x hx.1 hx.2
  · intro x hx y hy hxy
    rw [Finset.mem_coe, bc48_mem_classicalTrifFinset] at hx hy
    exact hinj x hx.1 hx.2 y hy.1 hy.2 hxy




theorem bc48_Tcount_classical_le_boundary_of_injection
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n) :
    ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n :=
  fun ω n => bc48_Tcount_classical_le_boundary_of_residue ω n (hres ω n)













theorem bc48_isOpenEdge_shift (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (x y : Site d) :
    IsOpenEdge d (shift g ω) (g • x) (g • y) ↔ IsOpenEdge d ω x y := by
  unfold IsOpenEdge
  rw [hyper_adj_smul, shift_apply_smul]




theorem bc48_isClassicalTrif_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bc47_IsClassicalTrifurcation (shift g ω) (g • x) ↔ bc47_IsClassicalTrifurcation ω x := by
  constructor
  · rintro ⟨a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩
    refine ⟨g⁻¹ • a₁, g⁻¹ • a₂, g⁻¹ • a₃, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun h => hne.1 ?_, fun h => hne.2.1 ?_, fun h => hne.2.2 ?_⟩ <;>
        · apply smul_injective g; simpa [smul_inv_smul] using h
    · 
      refine ⟨?_, ?_, ?_⟩
      · have := bc48_isOpenEdge_shift g ω x (g⁻¹ • a₁)
        rw [smul_inv_smul] at this; exact this.mp he1
      · have := bc48_isOpenEdge_shift g ω x (g⁻¹ • a₂)
        rw [smul_inv_smul] at this; exact this.mp he2
      · have := bc48_isOpenEdge_shift g ω x (g⁻¹ • a₃)
        rw [smul_inv_smul] at this; exact this.mp he3
    · 
      have hrm : ∀ a : Site d,
          cluster d (removeSite (g • x) (shift g ω)) (g • (g⁻¹ • a))
            = (fun y => g • y) '' cluster d (removeSite x ω) (g⁻¹ • a) := by
        intro a; rw [removeSite_shift]; exact cluster_shift g (removeSite x ω) (g⁻¹ • a)
      refine ⟨?_, ?_, ?_⟩
      · have h := hrm a₁; rw [smul_inv_smul] at h; rw [h] at hi1
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hi1
      · have h := hrm a₂; rw [smul_inv_smul] at h; rw [h] at hi2
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hi2
      · have h := hrm a₃; rw [smul_inv_smul] at h; rw [h] at hi3
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hi3
    · 
      refine ⟨?_, ?_, ?_⟩
      · intro hcon; apply hs12
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₂)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₁) (g⁻¹ • a₂)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this; exact this
      · intro hcon; apply hs13
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₁) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this; exact this
      · intro hcon; apply hs23
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₂)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₂) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this; exact this
  · rintro ⟨a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩
    refine ⟨g • a₁, g • a₂, g • a₃, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun h => hne.1 (smul_injective g h), fun h => hne.2.1 (smul_injective g h),
        fun h => hne.2.2 (smul_injective g h)⟩
    · exact ⟨(bc48_isOpenEdge_shift g ω x a₁).mpr he1,
        (bc48_isOpenEdge_shift g ω x a₂).mpr he2,
        (bc48_isOpenEdge_shift g ω x a₃).mpr he3⟩
    · 
      have hrm : ∀ a : Site d,
          cluster d (removeSite (g • x) (shift g ω)) (g • a)
            = (fun y => g • y) '' cluster d (removeSite x ω) a := by
        intro a; rw [removeSite_shift]; exact cluster_shift g (removeSite x ω) a
      refine ⟨?_, ?_, ?_⟩
      · rw [hrm a₁]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hi1
      · rw [hrm a₂]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hi2
      · rw [hrm a₃]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hi3
    · rw [removeSite_shift]
      exact ⟨fun hcon => hs12 ((connected_shift g (removeSite x ω) a₁ a₂).mp hcon),
        fun hcon => hs13 ((connected_shift g (removeSite x ω) a₁ a₃).mp hcon),
        fun hcon => hs23 ((connected_shift g (removeSite x ω) a₂ a₃).mp hcon)⟩



theorem bc48_measurableSet_clusterInfinite_removeSite (x a : Site d) :
    MeasurableSet
      {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite}
      = (fun ω => removeSite x ω) ⁻¹' {ω' | (cluster d ω' a).Infinite} := rfl
  rw [h]
  exact (measurable_removeSite x) (measurableSet_clusterInfinite a)



theorem bc48_measurableSet_isOpenEdge (x a : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | IsOpenEdge d ω x a} := by
  classical
  by_cases h : (hypercubicLattice d).Adj x a
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | IsOpenEdge d ω x a}
        = (fun ω => ω s(x, a)) ⁻¹' {true} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, IsOpenEdge]
      exact ⟨fun hh => hh.2, fun hh => ⟨h, hh⟩⟩
    rw [heq]
    exact (measurable_pi_apply (s(x, a) : Sym2 (Site d))) (measurableSet_singleton true)
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | IsOpenEdge d ω x a} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, IsOpenEdge, Set.mem_empty_iff_false, iff_false]
      exact fun hh => h hh.1
    rw [heq]; exact MeasurableSet.empty





theorem bc48_measurableSet_isClassicalTrifurcation (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | bc47_IsClassicalTrifurcation ω x} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | bc47_IsClassicalTrifurcation ω x}
      = ⋃ a₁ : Site d, ⋃ a₂ : Site d, ⋃ a₃ : Site d,
          ((if a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ then Set.univ else ∅)
            ∩ ({ω | IsOpenEdge d ω x a₁} ∩ {ω | IsOpenEdge d ω x a₂} ∩ {ω | IsOpenEdge d ω x a₃})
            ∩ ({ω | (cluster d (removeSite x ω) a₁).Infinite}
                ∩ {ω | (cluster d (removeSite x ω) a₂).Infinite}
                ∩ {ω | (cluster d (removeSite x ω) a₃).Infinite})
            ∩ ({ω | ¬ Connected d (removeSite x ω) a₁ a₂}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₁ a₃}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₂ a₃})) := by
    ext ω
    simp only [bc47_IsClassicalTrifurcation, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨a₁, a₂, a₃, hne, hopen, hinf, hsep⟩
      refine ⟨a₁, a₂, a₃, ⟨⟨⟨?_, ⟨⟨hopen.1, hopen.2.1⟩, hopen.2.2⟩⟩,
        ⟨⟨hinf.1, hinf.2.1⟩, hinf.2.2⟩⟩, ⟨⟨hsep.1, hsep.2.1⟩, hsep.2.2⟩⟩⟩
      rw [if_pos hne]; exact Set.mem_univ _
    · rintro ⟨a₁, a₂, a₃, ⟨⟨⟨hif, ⟨⟨ho1, ho2⟩, ho3⟩⟩, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩⟩
      by_cases hh : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃
      · exact ⟨a₁, a₂, a₃, hh, ⟨ho1, ho2, ho3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
      · rw [if_neg hh] at hif; exact absurd hif (Set.notMem_empty _)
  rw [heq]
  refine MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
    MeasurableSet.iUnion fun a₃ => ?_
  refine MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_) ?_
  · by_cases hh : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃
    · rw [if_pos hh]; exact MeasurableSet.univ
    · rw [if_neg hh]; exact MeasurableSet.empty
  · exact ((bc48_measurableSet_isOpenEdge x a₁).inter (bc48_measurableSet_isOpenEdge x a₂)).inter
      (bc48_measurableSet_isOpenEdge x a₃)
  · exact ((bc48_measurableSet_clusterInfinite_removeSite x a₁).inter
      (bc48_measurableSet_clusterInfinite_removeSite x a₂)).inter
      (bc48_measurableSet_clusterInfinite_removeSite x a₃)
  · exact (((measurableSet_connected_removeSite x a₁ a₂).compl).inter
      ((measurableSet_connected_removeSite x a₁ a₃).compl)).inter
      ((measurableSet_connected_removeSite x a₂ a₃).compl)













theorem bc48_classicalTrifProb_const (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (x : Site d) :
    μ {ω | bc47_IsClassicalTrifurcation ω x} = μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
  set g : Multiplicative (Site d) := Multiplicative.ofAdd x with hg
  have hgx : g • (0 : Site d) = x := by
    change Multiplicative.toAdd g + (0 : Site d) = x
    simp [hg]
  have hpre : (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹'
      {ω | bc47_IsClassicalTrifurcation ω x} = {ω | bc47_IsClassicalTrifurcation ω 0} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hgx, bc48_isClassicalTrif_shift g ω 0]
  calc μ {ω | bc47_IsClassicalTrifurcation ω x}
      = μ ((shift g) ⁻¹' {ω | bc47_IsClassicalTrifurcation ω x}) :=
        (hinv.measure_preimage g (bc48_measurableSet_isClassicalTrifurcation x)).symm
    _ = μ {ω | bc47_IsClassicalTrifurcation ω 0} := by rw [hpre]


theorem bc48_Tcount_classical_eq_sum_indicator (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (bc48_Tcount_classical d ω n : ℝ≥0∞) =
      ∑ x ∈ boxFinsetBK d n,
        ({ω' | bc47_IsClassicalTrifurcation ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
  classical
  rw [bc48_Tcount_classical_eq, bc48_classicalTrifFinset, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : bc47_IsClassicalTrifurcation ω x
  · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω' | bc47_IsClassicalTrifurcation ω' x} from h)]
  · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω' | bc47_IsClassicalTrifurcation ω' x} from h)]




theorem bc48_expected_Tcount_classical (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (n : ℕ) :
    ∫⁻ ω, (bc48_Tcount_classical d ω n : ℝ≥0∞) ∂μ
      = (boxFinsetBK d n).card • μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
  classical
  have hmeas : ∀ x : Site d, Measurable
      (fun ω => ({ω' | bc47_IsClassicalTrifurcation ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω) :=
    fun x => Measurable.indicator measurable_const (bc48_measurableSet_isClassicalTrifurcation x)
  calc ∫⁻ ω, (bc48_Tcount_classical d ω n : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑ x ∈ boxFinsetBK d n,
          ({ω' | bc47_IsClassicalTrifurcation ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        apply lintegral_congr; intro ω; exact bc48_Tcount_classical_eq_sum_indicator ω n
    _ = ∑ x ∈ boxFinsetBK d n,
          ∫⁻ ω, ({ω' | bc47_IsClassicalTrifurcation ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        rw [MeasureTheory.lintegral_finsetSum]
        intro x _; exact hmeas x
    _ = ∑ x ∈ boxFinsetBK d n, μ {ω | bc47_IsClassicalTrifurcation ω x} := by
        apply Finset.sum_congr rfl; intro x _
        rw [MeasureTheory.lintegral_indicator (bc48_measurableSet_isClassicalTrifurcation x)]; simp
    _ = ∑ _x ∈ boxFinsetBK d n, μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
        apply Finset.sum_congr rfl; intro x _; exact bc48_classicalTrifProb_const μ hinv x
    _ = (boxFinsetBK d n).card • μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
        rw [Finset.sum_const]





theorem bc48_classicalTrif_prob_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0)) :
    μ {ω | bc47_IsClassicalTrifurcation ω 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | bc47_IsClassicalTrifurcation ω 0} with hp
  have hkey : ∀ n, ((boxFinsetBK d n).card : ℝ≥0∞) * p ≤ (bdry n : ℝ≥0∞) := by
    intro n
    have hexp := bc48_expected_Tcount_classical μ hinv n
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ ω, (bc48_Tcount_classical d ω n : ℝ≥0∞) ∂μ ≤ (bdry n : ℝ≥0∞) := by
      calc ∫⁻ ω, (bc48_Tcount_classical d ω n : ℝ≥0∞) ∂μ
          ≤ ∫⁻ _ω, (bdry n : ℝ≥0∞) ∂μ := by
            apply lintegral_mono; intro ω; simp only; exact_mod_cast hbound ω n
        _ = (bdry n : ℝ≥0∞) := by rw [lintegral_const]; simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := by rw [hp]; exact (measure_ne_top μ _)
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ n, ((boxFinsetBK d n).card : ℝ) * pr ≤ (bdry n : ℝ) := by
    intro n
    have h := hkey n
    have h' : (((boxFinsetBK d n).card : ℝ≥0∞) * p).toReal ≤ (bdry n : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  have hvolr : ∀ n, (0 : ℝ) < ((boxFinsetBK d n).card : ℝ) := by
    intro n; exact_mod_cast hvol n
  have hle : ∀ n, pr ≤ (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ) := by
    intro n
    rw [le_div_iff₀ (hvolr n)]
    linarith [hkeyr n]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hdens hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this



















theorem bc48_numInfiniteClusters_ae_const_ne_top_classical
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | bc47_IsClassicalTrifurcation ω 0}) :
    ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
  
  have htri0 : μ {ω | bc47_IsClassicalTrifurcation ω 0} = 0 :=
    bc48_classicalTrif_prob_eq_zero μ herg.isTranslationInvariant bdry hbound hvol hdens
  
  have htop0 : μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
    by_contra h
    have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr h
    have := htrif hpos
    rw [htri0] at this
    exact (lt_irrefl 0) this
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const_uniqueness μ herg
  refine ⟨k, ?_, hk⟩
  intro hktop
  rw [hktop] at hk
  rw [hk] at htop0
  exact one_ne_zero htop0





theorem bc48_kne_top_classical
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | bc47_IsClassicalTrifurcation ω 0}) :
    ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
  intro k hk
  obtain ⟨k', hk'top, hk'⟩ :=
    bc48_numInfiniteClusters_ae_const_ne_top_classical μ herg bdry hbound hvol hdens htrif
  intro hktop
  have hsub : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω = k'}ᶜ := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hω]
    intro h; exact hk'top (by rw [← h, hktop])
  have hmk' : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'} := by
    have heq : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'}
        = numInfiniteClusters d ⁻¹' {k'} := by ext ω; simp [Set.mem_preimage]
    rw [heq]; exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
  have hfull : μ {ω | numInfiniteClusters d ω = k'}ᶜ = 1 :=
    le_antisymm prob_le_one (hk ▸ measure_mono hsub)
  have hnull : μ {ω | numInfiniteClusters d ω = k'} = 0 :=
    (prob_compl_eq_one_iff hmk').mp hfull
  rw [hk'] at hnull
  exact one_ne_zero hnull








theorem bc48_burton_keane_uniqueness_via_merge_classical
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | bc47_IsClassicalTrifurcation ω 0})
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ :=
    bc48_kne_top_classical μ herg bdry hbound hvol hdens htrif
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top hmergeGeom
  exact ⟨numInfiniteClusters_zero_or_one μ herg hmerge, hmerge,
    infiniteCluster_unique_ae μ herg hmerge⟩


















theorem bc48_burton_keane_bernoulli_classical (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | bc47_IsClassicalTrifurcation ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc48_burton_keane_uniqueness_via_merge_classical
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_isErgodic hd p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0)
    (fun n => boxSV_boundaryCard d n) hbound
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd) htrif
    (fun k hk2 hktop hk => hmergeGeom_discharged _ k hk2 hktop hk)







theorem bc48_burton_keane_bernoulli_of_classicalInjection (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | bc47_IsClassicalTrifurcation ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc48_burton_keane_bernoulli_classical hd p hp1 hp0
    (bc48_Tcount_classical_le_boundary_of_injection hinj) htrif




















theorem bc48_fakeConfig_hub_not_classicalTrif (n : ℕ) :
    bc47_x ∉ bc48_classicalTrifFinset bc47_fakeConfig n := by
  rw [bc48_mem_classicalTrifFinset]
  rintro ⟨_, hcl⟩
  exact bc47_not_classical_fakeConfig hcl





theorem bc48_fakeConfig_hub_in_ambient (n : ℕ) :
    bc47_x ∈ tfc_trifFinset bc47_fakeConfig n := by
  rw [tfc_mem_trifFinset]
  exact ⟨bc47_x_mem_box n, bc47_isTrifurcation_fakeConfig⟩






theorem bc48_fakeConfig_classical_proper_subset (n : ℕ) :
    bc48_classicalTrifFinset bc47_fakeConfig n ⊂ tfc_trifFinset bc47_fakeConfig n := by
  refine ⟨bc48_classicalTrifFinset_subset bc47_fakeConfig n, ?_⟩
  intro hsup
  exact bc48_fakeConfig_hub_not_classicalTrif n (hsup (bc48_fakeConfig_hub_in_ambient n))







theorem bc48_clawShadow_classical_fires :
    ∀ c : Fin 10, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) →
      ∃ n₁ n₂ n₃ : Fin 10,
        (bc46_clawLab c n₁ ≠ bc46_clawLab c n₂ ∧ bc46_clawLab c n₁ ≠ bc46_clawLab c n₃ ∧
          bc46_clawLab c n₂ ≠ bc46_clawLab c n₃) ∧
        (∃ z₁, bc46_clawLab c z₁ = bc46_clawLab c n₁ ∧ bc47_clawIsArm z₁ = true) ∧
        (∃ z₂, bc46_clawLab c z₂ = bc46_clawLab c n₂ ∧ bc47_clawIsArm z₂ = true) ∧
        (∃ z₃, bc46_clawLab c z₃ = bc46_clawLab c n₃ ∧ bc47_clawIsArm z₃ = true) :=
  bc47_clawShadow_classical_ok





theorem bc48_classicalInjection_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc48_ClassicalBoundaryArmInjection ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox hcl
    exact absurd (bc47_isTrifurcation_of_classical ω x hcl) (hno x hxbox)
  · intro x hxbox hcl
    exact absurd (bc47_isTrifurcation_of_classical ω x hcl) (hno x hxbox)



theorem bc48_Tcount_classical_eq_zero_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc48_Tcount_classical d ω n = 0 := by
  rw [bc48_Tcount_classical_eq, Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [bc48_mem_classicalTrifFinset] at hx
  exact hno x hx.1 (bc47_isTrifurcation_of_classical ω x hx.2)

end StatMech.Walls
