/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Percolation.DecoupledForestCount













namespace StatMech.Percolation

open StatMech StatMech.ConfigSpace MeasureTheory SimpleGraph Finset
open StatMech.Lattice
open scoped ENNReal

variable {d : ℕ}




theorem ctp_measurableSet_openAdj (x a : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x a} := by
  classical
  by_cases h : (hypercubicLattice d).Adj x a
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x a}
        = (fun ω => ω s(x, a)) ⁻¹' {true} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, openSubgraph_adj]
      exact ⟨fun hh => hh.2, fun hh => ⟨h, hh⟩⟩
    rw [heq]
    exact (measurable_pi_apply (s(x, a) : Sym2 (Site d))) (measurableSet_singleton true)
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x a} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, openSubgraph_adj, Set.mem_empty_iff_false, iff_false]
      exact fun hh => h hh.1
    rw [heq]; exact MeasurableSet.empty



theorem ctp_measurableSet_removeSiteClusterInfinite (x a : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite}
      = (fun ω => removeSite x ω) ⁻¹' {ω' | (cluster d ω' a).Infinite} := rfl
  rw [heq]
  exact (measurable_removeSite x) (measurableSet_clusterInfinite a)


theorem ctp_measurableSet_isCanonicalTrifurcation (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | IsCanonicalTrifurcation d ω x} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | IsCanonicalTrifurcation d ω x}
      = ⋃ a₁ : Site d, ⋃ a₂ : Site d, ⋃ a₃ : Site d,
          ((if a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ then Set.univ else ∅)
            ∩ ({ω | (openSubgraph d ω).Adj x a₁} ∩ {ω | (openSubgraph d ω).Adj x a₂}
                ∩ {ω | (openSubgraph d ω).Adj x a₃})
            ∩ ({ω | (cluster d (removeSite x ω) a₁).Infinite}
                ∩ {ω | (cluster d (removeSite x ω) a₂).Infinite}
                ∩ {ω | (cluster d (removeSite x ω) a₃).Infinite})
            ∩ ({ω | ¬ Connected d (removeSite x ω) a₁ a₂}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₁ a₃}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₂ a₃})) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩
      refine ⟨a₁, a₂, a₃, ⟨⟨⟨?_, ⟨⟨hadj.1, hadj.2.1⟩, hadj.2.2⟩⟩,
        ⟨⟨hinf.1, hinf.2.1⟩, hinf.2.2⟩⟩, ⟨⟨hsep.1, hsep.2.1⟩, hsep.2.2⟩⟩⟩
      rw [if_pos hne]; exact Set.mem_univ _
    · rintro ⟨a₁, a₂, a₃, ⟨⟨⟨hif, ⟨⟨hc1, hc2⟩, hc3⟩⟩, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩⟩
      by_cases hh : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃
      · exact ⟨a₁, a₂, a₃, hh, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
      · rw [if_neg hh] at hif; exact absurd hif (Set.notMem_empty _)
  rw [heq]
  refine MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
    MeasurableSet.iUnion fun a₃ => ?_
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  · by_cases hh : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃
    · rw [if_pos hh]; exact MeasurableSet.univ
    · rw [if_neg hh]; exact MeasurableSet.empty
  · exact ((ctp_measurableSet_openAdj x a₁).inter (ctp_measurableSet_openAdj x a₂)).inter
      (ctp_measurableSet_openAdj x a₃)
  · exact ((ctp_measurableSet_removeSiteClusterInfinite x a₁).inter
      (ctp_measurableSet_removeSiteClusterInfinite x a₂)).inter
      (ctp_measurableSet_removeSiteClusterInfinite x a₃)
  · exact (((measurableSet_connected_removeSite x a₁ a₂).compl).inter
      ((measurableSet_connected_removeSite x a₁ a₃).compl)).inter
      ((measurableSet_connected_removeSite x a₂ a₃).compl)




theorem ctp_isCanonicalTrifurcation_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    IsCanonicalTrifurcation d (shift g ω) (g • x) ↔ IsCanonicalTrifurcation d ω x := by
  constructor
  · rintro ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩
    refine ⟨g⁻¹ • a₁, g⁻¹ • a₂, g⁻¹ • a₃, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun h => hne.1 ?_, fun h => hne.2.1 ?_, fun h => hne.2.2 ?_⟩ <;>
        · apply smul_injective g; simpa [smul_inv_smul] using h
    · refine ⟨?_, ?_, ?_⟩
      · exact (openSubgraph_adj_shift g ω x (g⁻¹ • a₁)).mp (by rw [smul_inv_smul]; exact hadj.1)
      · exact (openSubgraph_adj_shift g ω x (g⁻¹ • a₂)).mp (by rw [smul_inv_smul]; exact hadj.2.1)
      · exact (openSubgraph_adj_shift g ω x (g⁻¹ • a₃)).mp (by rw [smul_inv_smul]; exact hadj.2.2)
    · refine ⟨?_, ?_, ?_⟩
      · have hc := cluster_shift g (removeSite x ω) (g⁻¹ • a₁)
        rw [smul_inv_smul, ← removeSite_shift] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.1
      · have hc := cluster_shift g (removeSite x ω) (g⁻¹ • a₂)
        rw [smul_inv_smul, ← removeSite_shift] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.2.1
      · have hc := cluster_shift g (removeSite x ω) (g⁻¹ • a₃)
        rw [smul_inv_smul, ← removeSite_shift] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.2.2
    · refine ⟨?_, ?_, ?_⟩
      · intro hcon
        apply hsep.1
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₂)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₁) (g⁻¹ • a₂)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this
        exact this
      · intro hcon
        apply hsep.2.1
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₁) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this
        exact this
      · intro hcon
        apply hsep.2.2
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₂)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₂) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this
        exact this
  · rintro ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩
    refine ⟨g • a₁, g • a₂, g • a₃, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun h => hne.1 (smul_injective g h), fun h => hne.2.1 (smul_injective g h),
        fun h => hne.2.2 (smul_injective g h)⟩
    · exact ⟨(openSubgraph_adj_shift g ω x a₁).mpr hadj.1,
        (openSubgraph_adj_shift g ω x a₂).mpr hadj.2.1,
        (openSubgraph_adj_shift g ω x a₃).mpr hadj.2.2⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [removeSite_shift g x ω, cluster_shift g (removeSite x ω) a₁]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.1
      · rw [removeSite_shift g x ω, cluster_shift g (removeSite x ω) a₂]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.1
      · rw [removeSite_shift g x ω, cluster_shift g (removeSite x ω) a₃]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.2
    · rw [removeSite_shift]
      exact ⟨fun hcon => hsep.1 ((connected_shift g (removeSite x ω) a₁ a₂).mp hcon),
        fun hcon => hsep.2.1 ((connected_shift g (removeSite x ω) a₁ a₃).mp hcon),
        fun hcon => hsep.2.2 ((connected_shift g (removeSite x ω) a₂ a₃).mp hcon)⟩


theorem ctp_canonicalTrifurcationProb_const (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (x : Site d) :
    μ {ω | IsCanonicalTrifurcation d ω x} = μ {ω | IsCanonicalTrifurcation d ω 0} := by
  set g : Multiplicative (Site d) := Multiplicative.ofAdd x with hg
  have hgx : g • (0 : Site d) = x := by
    show Multiplicative.toAdd g + (0 : Site d) = x
    simp [hg]
  have hpre : (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹'
      {ω | IsCanonicalTrifurcation d ω x} = {ω | IsCanonicalTrifurcation d ω 0} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hgx, ctp_isCanonicalTrifurcation_shift g ω 0]
  calc μ {ω | IsCanonicalTrifurcation d ω x}
      = μ ((shift g) ⁻¹' {ω | IsCanonicalTrifurcation d ω x}) :=
        (hinv.measure_preimage g (ctp_measurableSet_isCanonicalTrifurcation x)).symm
    _ = μ {ω | IsCanonicalTrifurcation d ω 0} := by rw [hpre]



open Classical in

lemma ctp_canonTcount_eq_sum_indicator (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (ctc2_canonTcount d ω n : ℝ≥0∞) =
      ∑ x ∈ boxFinsetBK d n,
        ({ω' | IsCanonicalTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
  classical
  unfold ctc2_canonTcount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : IsCanonicalTrifurcation d ω x
  · rw [if_pos h,
      Set.indicator_of_mem (show ω ∈ {ω' | IsCanonicalTrifurcation d ω' x} from h)]
  · rw [if_neg h,
      Set.indicator_of_notMem (show ω ∉ {ω' | IsCanonicalTrifurcation d ω' x} from h)]



theorem ctp_expected_canonTcount (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (n : ℕ) :
    ∫⁻ ω, (ctc2_canonTcount d ω n : ℝ≥0∞) ∂μ
      = (boxFinsetBK d n).card • μ {ω | IsCanonicalTrifurcation d ω 0} := by
  classical
  have hmeas : ∀ x : Site d, Measurable
      (fun ω => ({ω' | IsCanonicalTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω) :=
    fun x => Measurable.indicator measurable_const (ctp_measurableSet_isCanonicalTrifurcation x)
  calc ∫⁻ ω, (ctc2_canonTcount d ω n : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑ x ∈ boxFinsetBK d n,
          ({ω' | IsCanonicalTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        apply lintegral_congr; intro ω; exact ctp_canonTcount_eq_sum_indicator ω n
    _ = ∑ x ∈ boxFinsetBK d n,
          ∫⁻ ω, ({ω' | IsCanonicalTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        rw [MeasureTheory.lintegral_finsetSum]
        intro x _; exact hmeas x
    _ = ∑ x ∈ boxFinsetBK d n, μ {ω | IsCanonicalTrifurcation d ω x} := by
        apply Finset.sum_congr rfl; intro x _
        rw [MeasureTheory.lintegral_indicator (ctp_measurableSet_isCanonicalTrifurcation x)]; simp
    _ = ∑ _x ∈ boxFinsetBK d n, μ {ω | IsCanonicalTrifurcation d ω 0} := by
        apply Finset.sum_congr rfl; intro x _; exact ctp_canonicalTrifurcationProb_const μ hinv x
    _ = (boxFinsetBK d n).card • μ {ω | IsCanonicalTrifurcation d ω 0} := by
        rw [Finset.sum_const]






theorem ctp_canonical_trifurcation_prob_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0)) :
    μ {ω | IsCanonicalTrifurcation d ω 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | IsCanonicalTrifurcation d ω 0} with hp
  have hkey : ∀ n, 1 ≤ n →
      ((boxFinsetBK d n).card : ℝ≥0∞) * p ≤ (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) := by
    intro n hn
    have hexp := ctp_expected_canonTcount μ hinv n
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ ω, (ctc2_canonTcount d ω n : ℝ≥0∞) ∂μ
        ≤ (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) := by
      calc ∫⁻ ω, (ctc2_canonTcount d ω n : ℝ≥0∞) ∂μ
          ≤ ∫⁻ _ω, (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) ∂μ := by
            apply lintegral_mono; intro ω
            simp only
            exact_mod_cast dfc_canonTcount_le_boundary_succ ω n hn
        _ = (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) := by rw [lintegral_const]; simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := by rw [hp]; exact measure_ne_top μ _
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ n, 1 ≤ n →
      ((boxFinsetBK d n).card : ℝ) * pr ≤ (boxSV_boundaryCard d (n + 1) : ℝ) := by
    intro n hn
    have h := hkey n hn
    have h' : (((boxFinsetBK d n).card : ℝ≥0∞) * p).toReal
        ≤ (boxSV_boundaryCard d (n + 1) : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  have hvolr : ∀ n, (0 : ℝ) < ((boxFinsetBK d n).card : ℝ) := fun n => by exact_mod_cast hvol n
  have hle : ∀ n, 1 ≤ n →
      pr ≤ (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ) := by
    intro n hn
    rw [le_div_iff₀ (hvolr n)]
    linarith [hkeyr n hn]
  have hpr0 : pr ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hdens
      (Filter.eventually_atTop.mpr ⟨1, fun n hn => hle n hn⟩)
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this

end StatMech.Percolation
