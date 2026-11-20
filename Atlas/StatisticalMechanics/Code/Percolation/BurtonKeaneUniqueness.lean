/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Percolation.BurtonKeane
import Code.FK.FiniteEnergy

open MeasureTheory
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}










noncomputable def removeSite (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    ConfigSpace (Sym2 (Site d)) :=
  fun e => if x ∈ e then false else ω e

@[simp] lemma removeSite_apply_of_mem {x : Site d} {e : Sym2 (Site d)} (h : x ∈ e)
    (ω : ConfigSpace (Sym2 (Site d))) : removeSite x ω e = false := by
  simp [removeSite, h]

@[simp] lemma removeSite_apply_of_notMem {x : Site d} {e : Sym2 (Site d)} (h : x ∉ e)
    (ω : ConfigSpace (Sym2 (Site d))) : removeSite x ω e = ω e := by
  simp [removeSite, h]


theorem measurable_removeSite (x : Site d) :
    Measurable (fun ω : ConfigSpace (Sym2 (Site d)) => removeSite x ω) := by
  apply measurable_pi_lambda
  intro e
  unfold removeSite
  by_cases h : x ∈ e
  · simp [h]
  · simp only [h, if_false]; exact measurable_pi_apply e




theorem removeSite_shift (g : Multiplicative (Site d)) (x : Site d)
    (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite (g • x) (shift g ω) = shift g (removeSite x ω) := by
  funext e
  unfold removeSite
  rw [shift_apply, shift_apply]
  have hmem : (g • x ∈ e) ↔ (x ∈ g⁻¹ • e) := by
    constructor
    · intro h
      have : g⁻¹ • (g • x) ∈ g⁻¹ • e := Sym2.mem_map.mpr ⟨g • x, h, rfl⟩
      rwa [inv_smul_smul] at this
    · intro h
      have : g • x ∈ g • (g⁻¹ • e) := Sym2.mem_map.mpr ⟨x, h, rfl⟩
      rwa [smul_inv_smul] at this
  by_cases h : g • x ∈ e
  · rw [if_pos h, if_pos (hmem.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hmem.mpr hc))]













def IsTrifurcation (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    (Connected d ω x a₁ ∧ Connected d ω x a₂ ∧ Connected d ω x a₃) ∧
    ((cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite) ∧
    (¬ Connected d (removeSite x ω) a₁ a₂ ∧
      ¬ Connected d (removeSite x ω) a₁ a₃ ∧
      ¬ Connected d (removeSite x ω) a₂ a₃)




lemma measurableSet_connected_removeSite (x a b : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSite x ω) a b} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSite x ω) a b}
      = (fun ω => removeSite x ω) ⁻¹' {ω' | Connected d ω' a b} := rfl
  rw [h]
  exact (measurable_removeSite x) (measurableSet_connected a b)




theorem measurableSet_isTrifurcation (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | IsTrifurcation d ω x} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | IsTrifurcation d ω x}
      = ⋃ a₁ : Site d, ⋃ a₂ : Site d, ⋃ a₃ : Site d,
          ((if a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ then Set.univ else ∅)
            ∩ ({ω | Connected d ω x a₁} ∩ {ω | Connected d ω x a₂} ∩ {ω | Connected d ω x a₃})
            ∩ ({ω | (cluster d ω a₁).Infinite} ∩ {ω | (cluster d ω a₂).Infinite}
                ∩ {ω | (cluster d ω a₃).Infinite})
            ∩ ({ω | ¬ Connected d (removeSite x ω) a₁ a₂}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₁ a₃}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₂ a₃})) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨a₁, a₂, a₃, hne, hconn, hinf, hsep⟩
      refine ⟨a₁, a₂, a₃, ⟨⟨⟨?_, ⟨⟨hconn.1, hconn.2.1⟩, hconn.2.2⟩⟩,
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
  · exact ((measurableSet_connected x a₁).inter (measurableSet_connected x a₂)).inter
      (measurableSet_connected x a₃)
  · exact ((measurableSet_clusterInfinite a₁).inter (measurableSet_clusterInfinite a₂)).inter
      (measurableSet_clusterInfinite a₃)
  · exact (((measurableSet_connected_removeSite x a₁ a₂).compl).inter
      ((measurableSet_connected_removeSite x a₁ a₃).compl)).inter
      ((measurableSet_connected_removeSite x a₂ a₃).compl)






theorem isTrifurcation_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    IsTrifurcation d (shift g ω) (g • x) ↔ IsTrifurcation d ω x := by
  constructor
  · rintro ⟨a₁, a₂, a₃, hne, hconn, hinf, hsep⟩
    refine ⟨g⁻¹ • a₁, g⁻¹ • a₂, g⁻¹ • a₃, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun h => hne.1 ?_, fun h => hne.2.1 ?_, fun h => hne.2.2 ?_⟩ <;>
        · apply smul_injective g; simpa [smul_inv_smul] using h
    · refine ⟨?_, ?_, ?_⟩
      · exact (connected_shift g ω x (g⁻¹ • a₁)).mp (by rw [smul_inv_smul]; exact hconn.1)
      · exact (connected_shift g ω x (g⁻¹ • a₂)).mp (by rw [smul_inv_smul]; exact hconn.2.1)
      · exact (connected_shift g ω x (g⁻¹ • a₃)).mp (by rw [smul_inv_smul]; exact hconn.2.2)
    · refine ⟨?_, ?_, ?_⟩
      · have hc := cluster_shift g ω (g⁻¹ • a₁)
        rw [smul_inv_smul] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.1
      · have hc := cluster_shift g ω (g⁻¹ • a₂)
        rw [smul_inv_smul] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.2.1
      · have hc := cluster_shift g ω (g⁻¹ • a₃)
        rw [smul_inv_smul] at hc; rw [hc] at hinf
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
  · rintro ⟨a₁, a₂, a₃, hne, hconn, hinf, hsep⟩
    refine ⟨g • a₁, g • a₂, g • a₃, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun h => hne.1 (smul_injective g h), fun h => hne.2.1 (smul_injective g h),
        fun h => hne.2.2 (smul_injective g h)⟩
    · exact ⟨(connected_shift g ω x a₁).mpr hconn.1,
        (connected_shift g ω x a₂).mpr hconn.2.1,
        (connected_shift g ω x a₃).mpr hconn.2.2⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [cluster_shift g ω a₁]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.1
      · rw [cluster_shift g ω a₂]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.1
      · rw [cluster_shift g ω a₃]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.2
    · rw [removeSite_shift]
      exact ⟨fun hcon => hsep.1 ((connected_shift g (removeSite x ω) a₁ a₂).mp hcon),
        fun hcon => hsep.2.1 ((connected_shift g (removeSite x ω) a₁ a₃).mp hcon),
        fun hcon => hsep.2.2 ((connected_shift g (removeSite x ω) a₂ a₃).mp hcon)⟩




theorem trifurcationProb_const (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (x : Site d) :
    μ {ω | IsTrifurcation d ω x} = μ {ω | IsTrifurcation d ω 0} := by
  
  set g : Multiplicative (Site d) := Multiplicative.ofAdd x with hg
  have hgx : g • (0 : Site d) = x := by
    show Multiplicative.toAdd g + (0 : Site d) = x
    simp [hg]
  have hpre : (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹'
      {ω | IsTrifurcation d ω x} = {ω | IsTrifurcation d ω 0} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hgx, isTrifurcation_shift g ω 0]
  calc μ {ω | IsTrifurcation d ω x}
      = μ ((shift g) ⁻¹' {ω | IsTrifurcation d ω x}) :=
        (hinv.measure_preimage g (measurableSet_isTrifurcation x)).symm
    _ = μ {ω | IsTrifurcation d ω 0} := by rw [hpre]










noncomputable def boxFinsetBK (d n : ℕ) : Finset (Site d) := (box_finite d n).toFinset

open Classical in


noncomputable def Tcount (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : ℕ :=
  ((boxFinsetBK d n).filter (fun x => IsTrifurcation d ω x)).card



lemma Tcount_eq_sum_indicator (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (Tcount d ω n : ℝ≥0∞) =
      ∑ x ∈ boxFinsetBK d n,
        ({ω' | IsTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
  classical
  unfold Tcount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : IsTrifurcation d ω x
  · rw [if_pos h]
    rw [Set.indicator_of_mem (show ω ∈ {ω' | IsTrifurcation d ω' x} from h)]
  · rw [if_neg h]
    rw [Set.indicator_of_notMem (show ω ∉ {ω' | IsTrifurcation d ω' x} from h)]




theorem expected_Tcount (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (n : ℕ) :
    ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ
      = (boxFinsetBK d n).card • μ {ω | IsTrifurcation d ω 0} := by
  classical
  have hmeas : ∀ x : Site d, Measurable
      (fun ω => ({ω' | IsTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω) :=
    fun x => Measurable.indicator measurable_const (measurableSet_isTrifurcation x)
  calc ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑ x ∈ boxFinsetBK d n,
          ({ω' | IsTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        apply lintegral_congr; intro ω; exact Tcount_eq_sum_indicator ω n
    _ = ∑ x ∈ boxFinsetBK d n,
          ∫⁻ ω, ({ω' | IsTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        rw [MeasureTheory.lintegral_finsetSum]
        intro x _; exact hmeas x
    _ = ∑ x ∈ boxFinsetBK d n, μ {ω | IsTrifurcation d ω x} := by
        apply Finset.sum_congr rfl; intro x _
        rw [MeasureTheory.lintegral_indicator (measurableSet_isTrifurcation x)]; simp
    _ = ∑ _x ∈ boxFinsetBK d n, μ {ω | IsTrifurcation d ω 0} := by
        apply Finset.sum_congr rfl; intro x _; exact trifurcationProb_const μ hinv x
    _ = (boxFinsetBK d n).card • μ {ω | IsTrifurcation d ω 0} := by
        rw [Finset.sum_const]














theorem trifurcation_prob_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0)) :
    μ {ω | IsTrifurcation d ω 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | IsTrifurcation d ω 0} with hp
  
  have hkey : ∀ n, ((boxFinsetBK d n).card : ℝ≥0∞) * p ≤ (bdry n : ℝ≥0∞) := by
    intro n
    have hexp := expected_Tcount μ hinv n
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ ≤ (bdry n : ℝ≥0∞) := by
      calc ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ
          ≤ ∫⁻ _ω, (bdry n : ℝ≥0∞) ∂μ := by
            apply lintegral_mono; intro ω
            simp only
            exact_mod_cast hbound ω n
        _ = (bdry n : ℝ≥0∞) := by rw [lintegral_const]; simp
    rwa [hexp] at hle
  
  have hpfin : p ≠ ⊤ := by
    rw [hp]; exact (measure_ne_top μ _)
  
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
  have hpr0 : pr ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hdens hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this









theorem numInfiniteClusters_ae_const_uniqueness
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ) :
    ∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 :=
  numInfiniteClusters_ae_const μ herg






















theorem numInfiniteClusters_ae_const_ne_top
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    
    
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0}) :
    ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
  
  have htri0 : μ {ω | IsTrifurcation d ω 0} = 0 :=
    trifurcation_prob_eq_zero μ herg.isTranslationInvariant bdry hbound hvol hdens
  
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

end Percolation

end StatMech

