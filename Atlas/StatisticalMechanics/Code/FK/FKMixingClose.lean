/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.FK.Ergodicity
import Code.FK.IvPropertiesFull
import Code.FK.FKLimitsClose
import Code.FK.BulkDeviationProof
import Code.Foundations.Ergodicity
import Code.Inequalities.IncreasingEvent

open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]













def fmc_SelfMixing [Countable E] (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ A ∈ measurableCylinders (fun _ : E => Bool), ∀ ε : ℝ, 0 < ε →
    ∃ g : G, |μ.real (A ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A)
      - (μ.real A) ^ 2| < ε





theorem fmc_exists_cylinder_symmDiff_lt [Countable E] (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] {A : Set (ConfigSpace E)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C ∈ measurableCylinders (fun _ : E => Bool), μ (C ∆ A) < ε := by
  refine exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    isSetRing_measurableCylinders ?_ generateFrom_cylinders_eq hA hε
  exact ⟨{Set.univ}, Set.countable_singleton _,
    by simpa using univ_mem_measurableCylinders (fun _ : E => Bool), by simp⟩











theorem fmc_invariant_sq [Countable E] {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]
    (hμ : IsTranslationInvariant (G := G) μ) (hmix : fmc_SelfMixing (G := G) μ)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    μ.real s = (μ.real s) ^ 2 := by
  
  have key : ∀ ε : ℝ, 0 < ε → |μ.real s - (μ.real s) ^ 2| ≤ 5 * ε := by
    intro ε hε
    
    obtain ⟨C, hCmem, hCsd⟩ := fmc_exists_cylinder_symmDiff_lt μ hs
      (ε := ENNReal.ofReal ε) (by simpa using hε)
    have hCmeas : MeasurableSet C := MeasurableSet.of_mem_measurableCylinders hCmem
    
    obtain ⟨g, hg⟩ := hmix C hCmem ε hε
    set C' := (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C with hC'
    have hC'meas : MeasurableSet C' := hCmeas.preimage (measurable_shift g)
    
    have hCsd' : μ.real (C ∆ s) < ε := by
      have := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by simp)).2 hCsd
      rwa [ENNReal.toReal_ofReal hε.le] at this
    
    have hC'sd : μ.real (C' ∆ s) < ε := by
      have hpre_eq : C' ∆ s = (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' (C ∆ s) := by
        rw [hC', Set.preimage_symmDiff, hinv g]
      have : μ (C' ∆ s) = μ (C ∆ s) := by
        rw [hpre_eq]
        exact (hμ g).measure_preimage ((hCmeas.symmDiff hs).nullMeasurableSet)
      rw [Measure.real, this]; exact hCsd'
    
    have hCs : |μ.real C - μ.real s| ≤ μ.real (C ∆ s) :=
      abs_measureReal_sub_le_measureReal_symmDiff hCmeas.nullMeasurableSet hs.nullMeasurableSet
    
    have hint : |μ.real s - μ.real (C ∩ C')| ≤ μ.real (C ∆ s) + μ.real (C' ∆ s) := by
      have hsub : s ∆ (C ∩ C') ⊆ (s ∆ C) ∪ (s ∆ C') := by
        intro x hx
        rcases hx with ⟨hxs, hxCC'⟩ | ⟨hxCC', hxs⟩
        · rw [Set.mem_inter_iff, not_and_or] at hxCC'
          rcases hxCC' with hxC | hxC'
          · exact Or.inl (Or.inl ⟨hxs, hxC⟩)
          · exact Or.inr (Or.inl ⟨hxs, hxC'⟩)
        · obtain ⟨hxC, hxC'⟩ := hxCC'
          exact Or.inl (Or.inr ⟨hxC, hxs⟩)
      calc |μ.real s - μ.real (C ∩ C')|
          ≤ μ.real (s ∆ (C ∩ C')) :=
            abs_measureReal_sub_le_measureReal_symmDiff hs.nullMeasurableSet
              (hCmeas.inter hC'meas).nullMeasurableSet
        _ ≤ μ.real ((s ∆ C) ∪ (s ∆ C')) := measureReal_mono hsub (by finiteness)
        _ ≤ μ.real (s ∆ C) + μ.real (s ∆ C') := measureReal_union_le _ _
        _ = μ.real (C ∆ s) + μ.real (C' ∆ s) := by rw [symmDiff_comm, symmDiff_comm s C']
    
    have hmix' : |μ.real (C ∩ C') - (μ.real C) ^ 2| < ε := by rw [hC']; exact hg
    
    have habs1 : |(μ.real C) ^ 2 - (μ.real s) ^ 2| ≤ 2 * μ.real (C ∆ s) := by
      have hCnn : 0 ≤ μ.real C := measureReal_nonneg
      have hsnn : 0 ≤ μ.real s := measureReal_nonneg
      have hle1 : μ.real C ≤ 1 := measureReal_le_one
      have hle1s : μ.real s ≤ 1 := measureReal_le_one
      calc |μ.real C ^ 2 - μ.real s ^ 2|
          = |μ.real C - μ.real s| * |μ.real C + μ.real s| := by rw [← abs_mul]; ring_nf
        _ ≤ |μ.real C - μ.real s| * 2 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [abs_of_nonneg (by positivity)]; linarith
        _ ≤ μ.real (C ∆ s) * 2 := mul_le_mul_of_nonneg_right hCs (by norm_num)
        _ = 2 * μ.real (C ∆ s) := by ring
    
    have htri : |μ.real s - (μ.real s) ^ 2|
        ≤ |μ.real s - μ.real (C ∩ C')|
          + (|μ.real (C ∩ C') - (μ.real C) ^ 2| + |(μ.real C) ^ 2 - (μ.real s) ^ 2|) := by
      have h1 := abs_sub_le (μ.real s) (μ.real (C ∩ C')) ((μ.real s) ^ 2)
      have h2 := abs_sub_le (μ.real (C ∩ C')) ((μ.real C) ^ 2) ((μ.real s) ^ 2)
      calc |μ.real s - (μ.real s) ^ 2|
          ≤ |μ.real s - μ.real (C ∩ C')| + |μ.real (C ∩ C') - (μ.real s) ^ 2| := h1
        _ ≤ |μ.real s - μ.real (C ∩ C')|
            + (|μ.real (C ∩ C') - (μ.real C) ^ 2| + |(μ.real C) ^ 2 - (μ.real s) ^ 2|) := by
              linarith
    have hCsd0 : (0 : ℝ) ≤ μ.real (C ∆ s) := measureReal_nonneg
    have hC'sd0 : (0 : ℝ) ≤ μ.real (C' ∆ s) := measureReal_nonneg
    calc |μ.real s - (μ.real s) ^ 2|
        ≤ |μ.real s - μ.real (C ∩ C')|
          + (|μ.real (C ∩ C') - (μ.real C) ^ 2| + |(μ.real C) ^ 2 - (μ.real s) ^ 2|) := htri
      _ ≤ (μ.real (C ∆ s) + μ.real (C' ∆ s)) + (ε + 2 * μ.real (C ∆ s)) :=
          add_le_add hint (add_le_add hmix'.le habs1)
      _ ≤ (ε + ε) + (ε + 2 * ε) :=
          add_le_add (add_le_add hCsd'.le hC'sd.le) (add_le_add le_rfl (by linarith))
      _ ≤ 5 * ε := by linarith
  
  have hzero : |μ.real s - (μ.real s) ^ 2| = 0 := by
    by_contra hne
    have hpos : 0 < |μ.real s - (μ.real s) ^ 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have := key (|μ.real s - (μ.real s) ^ 2| / 8) (by positivity)
    linarith
  have := abs_eq_zero.mp hzero; linarith



theorem fmc_real_zero_or_one {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]
    {s : Set (ConfigSpace E)} (hsq : μ.real s = (μ.real s) ^ 2) :
    μ s = 0 ∨ μ s = μ Set.univ := by
  have hreal01 : μ.real s = 0 ∨ μ.real s = 1 := by
    have : μ.real s * (μ.real s - 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hreal01 with h0 | h1
  · left
    have : μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
    rw [this, h0, ENNReal.ofReal_zero]
  · right
    rw [measure_univ]
    have : μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
    rw [this, h1, ENNReal.ofReal_one]














theorem fmc_isErgodic_of_selfMixing [Countable E] {μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] (hμ : IsTranslationInvariant (G := G) μ)
    (hmix : fmc_SelfMixing (G := G) μ) :
    IsErgodic (G := G) μ := by
  refine ⟨hμ, ?_⟩
  intro s hs hinv
  exact fmc_real_zero_or_one (fmc_invariant_sq hμ hmix hs hinv)










theorem fmc_shift_isIncreasing {A : Set (ConfigSpace E)} (hA : IsIncreasing A) (g : G) :
    IsIncreasing ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A) := by
  intro x y hxy hx
  simp only [Set.mem_preimage] at hx ⊢
  refine hA ?_ hx
  intro e; simpa [shift] using hxy (g⁻¹ • e)


theorem fmc_real_preimage_shift {μ : Measure (ConfigSpace E)}
    (hμ : IsTranslationInvariant (G := G) μ) (g : G) {A : Set (ConfigSpace E)}
    (hA : MeasurableSet A) :
    μ.real ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A) = μ.real A := by
  unfold Measure.real
  rw [(hμ g).measure_preimage hA.nullMeasurableSet]
















theorem fmc_fkg_lower_bound {μ : Measure (ConfigSpace E)}
    (hμ : IsTranslationInvariant (G := G) μ)
    (hPA : ∀ {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) (hAmeas : MeasurableSet A) (g : G) :
    (μ.real A) ^ 2 ≤ μ.real (A ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A) := by
  have hA' : IsIncreasing ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A) :=
    fmc_shift_isIncreasing hA g
  have hA'meas : MeasurableSet ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A) :=
    hAmeas.preimage (measurable_shift g)
  have hPAbound := hPA hA hA' hAmeas hA'meas
  rw [fmc_real_preimage_shift hμ g hAmeas] at hPAbound
  calc (μ.real A) ^ 2 = μ.real A * μ.real A := sq (μ.real A)
    _ ≤ μ.real (A ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A) := hPAbound







variable {d : ℕ}










theorem fmc_wiredIV_isErgodic_of_mixing {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hmix : fmc_SelfMixing (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmc_isErgodic_of_selfMixing (flc_wiredIV_isTranslationInvariant hp hp1) hmix




theorem fmc_freeIV_isErgodic_of_mixing {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hmix : fmc_SelfMixing (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmc_isErgodic_of_selfMixing (bdp_freeIV_isTranslationInvariant hp hp1) hmix








example : True := by
  have h : ∀ (hmix : fmc_SelfMixing (G := Multiplicative (Site 2))
      (wiredInfiniteVolume 2 (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 < 1)
          (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site 2))))), True := by
    intro hmix
    have := fmc_wiredIV_isErgodic_of_mixing (p := 1/2) (by norm_num) (by norm_num) hmix
    trivial
  trivial

end FK

end StatMech
