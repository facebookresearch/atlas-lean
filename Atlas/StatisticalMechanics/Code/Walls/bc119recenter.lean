/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Walls.bc117mergeproof

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}











theorem bc119_shell_of_walk_into_box_y {L : ℕ} {y : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    {b u x : Site 2} (w : (openSubgraph 2 ω).Walk u x) :
    Connected 2 (removeSites (bc61_boxAround 2 L y) ω) b u → u ∉ bc61_boxAround 2 L y →
    x ∈ bc61_boxAround 2 L y →
    ∃ s t : Site 2, (openSubgraph 2 ω).Adj s t ∧
      t ∈ bc61_boxAround 2 L y ∧
      Connected 2 (removeSites (bc61_boxAround 2 L y) ω) b s := by
  induction w with
  | nil =>
    intro _ hu hx; exact absurd hx hu
  | @cons u v z hadj w' ih =>
    intro hbu hu hx
    by_cases hv : v ∈ bc61_boxAround 2 L y
    · exact ⟨u, v, hadj, hv, hbu⟩
    · have hstep : Connected 2 (removeSites (bc61_boxAround 2 L y) ω) u v :=
        bc117_cut_step_of_notMem hadj hu hv
      exact ih (hbu.trans hstep) hv hx






theorem bc119_attach_of_meetsBox_y {L : ℕ} {y : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    {x x' : Site 2} (hinf : (cluster 2 ω x).Infinite) (hx'box : x' ∈ bc61_boxAround 2 L y)
    (hxx' : cluster 2 ω x = cluster 2 ω x') :
    ∃ a : Site 2,
      (∃ bx ∈ bc61_boxAround 2 L y, (openSubgraph 2 ω).Adj bx a) ∧
      (cluster 2 (removeSites (bc61_boxAround 2 L y) ω) a).Infinite ∧
      cluster 2 ω x = cluster 2 ω a := by
  classical
  obtain ⟨b, hbconn, hbnot, hbinf⟩ :=
    bc117_boxAvoiding_external_infinite ω hinf (bc61_boxAround 2 L y)
  have hxx'conn : Connected 2 ω x x' := by
    have : x' ∈ cluster 2 ω x := by rw [hxx']; exact self_mem_cluster ω x'
    exact mem_cluster.mp this
  have hbx' : Connected 2 ω b x' := hbconn.symm.trans hxx'conn
  obtain ⟨w⟩ := hbx'
  obtain ⟨s, t, hadj, htbox, hscut⟩ :=
    bc119_shell_of_walk_into_box_y (b := b) w (connected_refl _ b) hbnot hx'box
  refine ⟨s, ⟨t, htbox, hadj.symm⟩, ?_, ?_⟩
  · have hcl : cluster 2 (removeSites (bc61_boxAround 2 L y) ω) b
        = cluster 2 (removeSites (bc61_boxAround 2 L y) ω) s :=
      cluster_eq_of_connected hscut
    rwa [hcl] at hbinf
  · have hbs : Connected 2 ω b s := bc61_connected_of_cut hscut
    have : Connected 2 ω x s := hbconn.trans hbs
    exact cluster_eq_of_connected this








theorem bc119_merge_at_y {L : ℕ} {y : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    {x₁ x₂ x₃ : Site 2}
    (hi₁ : (cluster 2 ω x₁).Infinite) (hi₂ : (cluster 2 ω x₂).Infinite)
    (hi₃ : (cluster 2 ω x₃).Infinite)
    (hd₁₂ : cluster 2 ω x₁ ≠ cluster 2 ω x₂) (hd₁₃ : cluster 2 ω x₁ ≠ cluster 2 ω x₃)
    (hd₂₃ : cluster 2 ω x₂ ≠ cluster 2 ω x₃)
    (hm₁ : ∃ x₁' ∈ bc61_boxAround 2 L y, cluster 2 ω x₁ = cluster 2 ω x₁')
    (hm₂ : ∃ x₂' ∈ bc61_boxAround 2 L y, cluster 2 ω x₂ = cluster 2 ω x₂')
    (hm₃ : ∃ x₃' ∈ bc61_boxAround 2 L y, cluster 2 ω x₃ = cluster 2 ω x₃') :
    bc61_IsCoarseTrifurcation ω L y := by
  obtain ⟨x₁', hb₁', hc₁⟩ := hm₁
  obtain ⟨x₂', hb₂', hc₂⟩ := hm₂
  obtain ⟨x₃', hb₃', hc₃⟩ := hm₃
  obtain ⟨a₁, hadj₁, hinf₁, he₁⟩ := bc119_attach_of_meetsBox_y hi₁ hb₁' hc₁
  obtain ⟨a₂, hadj₂, hinf₂, he₂⟩ := bc119_attach_of_meetsBox_y hi₂ hb₂' hc₂
  obtain ⟨a₃, hadj₃, hinf₃, he₃⟩ := bc119_attach_of_meetsBox_y hi₃ hb₃' hc₃
  have hda₁₂ : cluster 2 ω a₁ ≠ cluster 2 ω a₂ := by rw [← he₁, ← he₂]; exact hd₁₂
  have hda₁₃ : cluster 2 ω a₁ ≠ cluster 2 ω a₃ := by rw [← he₁, ← he₃]; exact hd₁₃
  have hda₂₃ : cluster 2 ω a₂ ≠ cluster 2 ω a₃ := by rw [← he₂, ← he₃]; exact hd₂₃
  exact ⟨a₁, a₂, a₃, hadj₁, hadj₂, hadj₃, ⟨hinf₁, hinf₂, hinf₃⟩,
    bc115_disconnected_of_distinctClusters _ ω hda₁₂,
    bc115_disconnected_of_distinctClusters _ ω hda₁₃,
    bc115_disconnected_of_distinctClusters _ ω hda₂₃⟩













theorem bc119_merge_recentered {L : ℕ} {y : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    {x₁ x₂ x₃ : Site 2}
    (hi₁ : (cluster 2 ω x₁).Infinite) (hi₂ : (cluster 2 ω x₂).Infinite)
    (hi₃ : (cluster 2 ω x₃).Infinite)
    (hd₁₂ : cluster 2 ω x₁ ≠ cluster 2 ω x₂) (hd₁₃ : cluster 2 ω x₁ ≠ cluster 2 ω x₃)
    (hd₂₃ : cluster 2 ω x₂ ≠ cluster 2 ω x₃)
    (hb₁ : x₁ ∈ bc61_boxAround 2 L y) (hb₂ : x₂ ∈ bc61_boxAround 2 L y)
    (hb₃ : x₃ ∈ bc61_boxAround 2 L y) :
    bc61_IsCoarseTrifurcation ω L y :=
  bc119_merge_at_y hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
    ⟨x₁, hb₁, rfl⟩ ⟨x₂, hb₂, rfl⟩ ⟨x₃, hb₃, rfl⟩






theorem bc119_commonBox_of_close {L : ℕ} {x₁ x₂ x₃ : Site 2}
    (h₂ : ∀ i, (x₂ i - x₁ i).natAbs ≤ L) (h₃ : ∀ i, (x₃ i - x₁ i).natAbs ≤ L) :
    x₁ ∈ bc61_boxAround 2 L x₁ ∧ x₂ ∈ bc61_boxAround 2 L x₁ ∧ x₃ ∈ bc61_boxAround 2 L x₁ := by
  have hself : x₁ ∈ bc61_boxAround 2 L x₁ := by
    rw [bc61_mem_boxAround, mem_box]; intro i; simp
  refine ⟨hself, ?_, ?_⟩
  · rw [bc61_mem_boxAround, mem_box]; intro i; simpa using h₂ i
  · rw [bc61_mem_boxAround, mem_box]; intro i; simpa using h₃ i





theorem bc119_merge_recentered_of_close {L : ℕ} {ω : ConfigSpace (Sym2 (Site 2))}
    {x₁ x₂ x₃ : Site 2}
    (hi₁ : (cluster 2 ω x₁).Infinite) (hi₂ : (cluster 2 ω x₂).Infinite)
    (hi₃ : (cluster 2 ω x₃).Infinite)
    (hd₁₂ : cluster 2 ω x₁ ≠ cluster 2 ω x₂) (hd₁₃ : cluster 2 ω x₁ ≠ cluster 2 ω x₃)
    (hd₂₃ : cluster 2 ω x₂ ≠ cluster 2 ω x₃)
    (h₂ : ∀ i, (x₂ i - x₁ i).natAbs ≤ L) (h₃ : ∀ i, (x₃ i - x₁ i).natAbs ≤ L) :
    bc61_IsCoarseTrifurcation ω L x₁ := by
  obtain ⟨hb₁, hb₂, hb₃⟩ := bc119_commonBox_of_close h₂ h₃
  exact bc119_merge_recentered hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃ hb₁ hb₂ hb₃













theorem bc119_originCoarseTrif_of_yCoarseTrif
    (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (L : ℕ) {y : Site d}
    (hy : 0 < μ {ω | bc61_IsCoarseTrifurcation ω L y}) :
    0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
  rwa [bc62_coarseTrifProb_const μ hinv L y] at hy










theorem bc119_coarseTrifExistence_of_recentered
    (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (L : ℕ)
    (hrec : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ y : Site d, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L y}) :
    bc61_CoarseTrifExistence μ L := by
  intro htop
  obtain ⟨y, hy⟩ := hrec htop
  exact bc119_originCoarseTrif_of_yCoarseTrif μ hinv L hy

















def bc119_RecenterBoxMerge (d L n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∀ x₁ x₂ x₃ : Site d,
    x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
    (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
    cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
    cluster d ω x₂ ≠ cluster d ω x₃ →
    ∃ (y : Site d) (W : Finset (Sym2 (Site d))),
      bc61_IsCoarseTrifurcation (forceOpenFinset W ω) L y




theorem bc119_recenterBoxRoute_of_residue {L n : ℕ} (hres : bc119_RecenterBoxMerge d L n)
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    ∃ (y : Site d) (W : Finset (Sym2 (Site d))),
      bc61_IsCoarseTrifurcation (forceOpenFinset W ω) L y := by
  obtain ⟨x₁, x₂, x₃, ⟨hb1, hb2, hb3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ :=
    tfe_three_distinct_infinite_of_box hω
  exact hres ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23




theorem bc119_coarseTrifCover_of_residue {L n : ℕ} (hres : bc119_RecenterBoxMerge d L n) :
    threeMeetBox d n ⊆
      ⋃ (y : Site d) (W : Finset (Sym2 (Site d))),
        (fun ω => forceOpenFinset W ω) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L y} := by
  intro ω hω
  obtain ⟨y, W, htrif⟩ := bc119_recenterBoxRoute_of_residue hres hω
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
  exact ⟨y, W, htrif⟩









theorem bc119_originCoarseTrif_at_of_residue
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) {L n : ℕ} (hres : bc119_RecenterBoxMerge d L n)
    (hpos : 0 < μ (threeMeetBox d n)) :
    0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
  classical
  set ι := Site d × Finset (Sym2 (Site d)) with hι
  set B : ι → Set (ConfigSpace (Sym2 (Site d))) :=
    fun p => (fun ω => forceOpenFinset p.2 ω) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L p.1} with hB
  have hcover : threeMeetBox d n ⊆ ⋃ p : ι, B p := by
    intro ω hω
    obtain ⟨y, W, htrif⟩ := bc119_recenterBoxRoute_of_residue hres hω
    exact Set.mem_iUnion.mpr ⟨(y, W), by simpa [hB, Set.mem_preimage] using htrif⟩
  obtain ⟨p, hppos⟩ := DisjointPaths.exists_pos_of_cover μ hcover hpos
  obtain ⟨y, W⟩ := p
  have hy : 0 < μ {ω | bc61_IsCoarseTrifurcation ω L y} :=
    DisjointPaths.pos_of_forceOpen_preimage μ hfe W (bc62_measurableSet_coarseTrif L y) subset_rfl hppos
  exact bc119_originCoarseTrif_of_yCoarseTrif μ hinv L hy










theorem bc119_coarseTrifExistence_of_recenterResidue
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ) (hres : ∀ n : ℕ, bc119_RecenterBoxMerge d L n) :
    bc61_CoarseTrifExistence μ L := by
  intro htop
  obtain ⟨n, hnpos⟩ := exists_threeMeetBox_pos μ htop
  exact bc119_originCoarseTrif_at_of_residue μ hinv hfe (hres n) hnpos










theorem bc119_recenterBoxMerge_of_origin {L n : ℕ}
    (hmerge : bc115_CoarseTrifMerge d L n) : bc119_RecenterBoxMerge d L n := by
  intro ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  obtain ⟨W, htrif⟩ := hmerge ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  exact ⟨0, W, htrif⟩











theorem bc119_recenter_upperLines_witness {L : ℕ} (hL : 3 ≤ L) :
    ∃ (y : Site 2) (W : Finset (Sym2 (Site 2))),
      bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L y := by
  refine ⟨0, ∅, ?_⟩
  rw [bc115_forceOpen_empty]
  exact bc61_wholeBox_severs_upperLines hL























































theorem bc119_status :
    
    (∀ {L : ℕ} {y : Site 2} {ω : ConfigSpace (Sym2 (Site 2))} {x x' : Site 2},
      (cluster 2 ω x).Infinite → x' ∈ bc61_boxAround 2 L y → cluster 2 ω x = cluster 2 ω x' →
      ∃ a : Site 2,
        (∃ bx ∈ bc61_boxAround 2 L y, (openSubgraph 2 ω).Adj bx a) ∧
        (cluster 2 (removeSites (bc61_boxAround 2 L y) ω) a).Infinite ∧
        cluster 2 ω x = cluster 2 ω a) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))),
      IsTranslationInvariant (G := Multiplicative (Site d)) μ → ∀ (L : ℕ) (y : Site d),
      0 < μ {ω | bc61_IsCoarseTrifurcation ω L y} → 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0}) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ],
      IsTranslationInvariant (G := Multiplicative (Site d)) μ → HasFiniteEnergyMerge μ →
      ∀ (L : ℕ), (∀ n : ℕ, bc119_RecenterBoxMerge d L n) → bc61_CoarseTrifExistence μ L) ∧
    
    (∀ (L n : ℕ), bc115_CoarseTrifMerge d L n → bc119_RecenterBoxMerge d L n) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      ∃ (y : Site 2) (W : Finset (Sym2 (Site 2))),
        bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro L y ω x x' hinf hx'box hxx'; exact bc119_attach_of_meetsBox_y hinf hx'box hxx'
  · intro μ hinv L y hy; exact bc119_originCoarseTrif_of_yCoarseTrif μ hinv L hy
  · intro μ _ hinv hfe L hres; exact bc119_coarseTrifExistence_of_recenterResidue μ hinv hfe L hres
  · intro L n hmerge; exact bc119_recenterBoxMerge_of_origin hmerge
  · intro L hL; exact bc119_recenter_upperLines_witness hL

end StatMech.Walls
