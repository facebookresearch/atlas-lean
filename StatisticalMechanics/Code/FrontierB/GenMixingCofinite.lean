/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.FreeDLRExtreme
import Code.FrontierB.PairMixingCofinite

open MeasureTheory Set
open StatMech.ConfigSpace
open scoped symmDiff

namespace StatMech.FrontierB

open StatMech.FK

variable {E G : Type*} [Countable E] [CommGroup G] [MulAction G E]


theorem isClopen_of_mem_measurableCylinders_bool
    {A : Set (ConfigSpace E)}
    (hA : A ∈ measurableCylinders (fun _ : E => Bool)) : IsClopen A := by
  rw [mem_measurableCylinders] at hA
  obtain ⟨F, S, _, rfl⟩ := hA
  exact isClopen_cylinderEvent F S



theorem isClopen_mem_measurableCylinders_bool
    (A : Set (ConfigSpace E)) (hA : IsClopen A) :
    A ∈ measurableCylinders (fun _ : E => Bool) := by
  classical
  obtain ⟨F, hF⟩ := isClopen_dependsOn_finset A hA
  rw [mem_measurableCylinders]
  refine ⟨F, ih_section A F, MeasurableSet.of_discrete, ?_⟩
  exact ih_eq_cylinder_of_dependsOn F hF



theorem fmu_genMixing_exists_not_mem [Infinite G]
    {mu : Measure (ConfigSpace E)} [IsProbabilityMeasure mu]
    (hti : IsTranslationInvariant (G := G) mu)
    (hmix : fmu_GenMixing (G := G) mu)
    (family : Finset (Set (ConfigSpace E)))
    (hfamily : ∀ A ∈ family,
      A ∈ measurableCylinders (fun _ : E => Bool))
    (K : Finset G) (delta : Real) (hdelta : 0 < delta) :
    ∃ g : G, g ∉ K ∧ ∀ A ∈ family, ∀ B ∈ family,
      abs (mu.real (A ∩
          (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' B) -
        mu.real A * mu.real B) < delta := by
  classical
  obtain ⟨L, hL⟩ := Finset.exists_card_eq (α := G) (K.card + 1)
  let translated : G → Set (ConfigSpace E) → Set (ConfigSpace E) :=
    fun k A => (shift k : ConfigSpace E → ConfigSpace E) ⁻¹' A
  let enlarged : Finset (Set (ConfigSpace E)) :=
    family ∪ L.biUnion (fun k => family.image (translated k))
  have henlarged : ∀ A ∈ enlarged,
      A ∈ measurableCylinders (fun _ : E => Bool) := by
    intro A hA
    rw [Finset.mem_union] at hA
    rcases hA with hA | hA
    · exact hfamily A hA
    · rw [Finset.mem_biUnion] at hA
      obtain ⟨k, hk, hA⟩ := hA
      rw [Finset.mem_image] at hA
      obtain ⟨B, hB, rfl⟩ := hA
      apply isClopen_mem_measurableCylinders_bool
      exact (isClopen_of_mem_measurableCylinders_bool
        (hfamily B hB)).preimage (continuous_shift k)
  obtain ⟨h, hh⟩ := hmix enlarged henlarged delta hdelta
  have hexists : ∃ k ∈ L, h * k ∉ K := by
    by_contra hcontra
    push Not at hcontra
    have hsub : L.image (fun k => h * k) ⊆ K := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact hcontra k hk
    have hcard := Finset.card_le_card hsub
    have hinj : Function.Injective (fun k : G => h * k) := by
      intro a b hab
      exact mul_left_cancel hab
    rw [Finset.card_image_of_injective _ hinj, hL] at hcard
    omega
  obtain ⟨k, hkL, hkK⟩ := hexists
  refine ⟨h * k, hkK, ?_⟩
  intro A hAf B hBf
  let Bk := translated k B
  have hAenlarged : A ∈ enlarged := Finset.mem_union_left _ hAf
  have hBkenlarged : Bk ∈ enlarged := by
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    exact ⟨k, hkL, Finset.mem_image.mpr ⟨B, hBf, rfl⟩⟩
  have hgood := hh A hAenlarged Bk hBkenlarged
  have hcross : A ∩
        (shift h : ConfigSpace E → ConfigSpace E) ⁻¹' Bk =
      A ∩ (shift (h * k) : ConfigSpace E → ConfigSpace E) ⁻¹' B := by
    ext omega
    simp only [Bk, translated, mem_inter_iff, mem_preimage]
    rw [mul_comm h k, shift_mul]
    rfl
  have hmass : mu.real Bk = mu.real B := by
    exact fmc_real_preimage_shift hti k
      (MeasurableSet.of_mem_measurableCylinders (hfamily B hBf))
  rwa [hcross, hmass] at hgood



theorem fmu_genMixing_event_exists_not_mem [Infinite G]
    {mu : Measure (ConfigSpace E)} [IsProbabilityMeasure mu]
    (hti : IsTranslationInvariant (G := G) mu)
    (hmix : fmu_GenMixing (G := G) mu)
    (s : Set (ConfigSpace E)) (hs : MeasurableSet s)
    (K : Finset G) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : G, g ∉ K ∧
      abs (mu.real (s ∩
          (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s) -
        (mu.real s) ^ 2) < 5 * epsilon := by
  obtain ⟨C, hCmem, hCsd⟩ := fmc_exists_cylinder_symmDiff_lt mu hs
    (ε := ENNReal.ofReal epsilon) (by simpa using hepsilon)
  have hCmeas : MeasurableSet C :=
    MeasurableSet.of_mem_measurableCylinders hCmem
  obtain ⟨g, hgK, hmixC⟩ := fmu_genMixing_exists_not_mem
    hti hmix {C} (by
      intro A hA
      have hAC : A = C := Finset.mem_singleton.mp hA
      rw [hAC]
      exact hCmem) K epsilon hepsilon
  refine ⟨g, hgK, ?_⟩
  let C' := (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C
  let s' := (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s
  have hC'meas : MeasurableSet C' :=
    hCmeas.preimage (measurable_shift g)
  have hs'meas : MeasurableSet s' :=
    hs.preimage (measurable_shift g)
  have hCsd' : mu.real (C ∆ s) < epsilon := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top mu _) (by simp)).2 hCsd
    rwa [ENNReal.toReal_ofReal hepsilon.le] at h
  have hC'sd' : mu.real (C' ∆ s') < epsilon := by
    have hpre : C' ∆ s' =
        (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' (C ∆ s) := by
      ext x
      rfl
    have hmeasure : mu (C' ∆ s') = mu (C ∆ s) := by
      rw [hpre]
      exact (hti g).measure_preimage
        ((hCmeas.symmDiff hs).nullMeasurableSet)
    rw [Measure.real, hmeasure]
    exact hCsd'
  have hCs : abs (mu.real C - mu.real s) ≤ mu.real (C ∆ s) :=
    abs_measureReal_sub_le_measureReal_symmDiff
      hCmeas.nullMeasurableSet hs.nullMeasurableSet
  have hinter : abs (mu.real (C ∩ C') - mu.real (s ∩ s')) ≤
      mu.real (C ∆ s) + mu.real (C' ∆ s') := by
    have hsub : (C ∩ C') ∆ (s ∩ s') ⊆
        (C ∆ s) ∪ (C' ∆ s') := by
      intro x hx
      rcases hx with ⟨hxCC', hxss'⟩ | ⟨hxss', hxCC'⟩
      · obtain ⟨hxC, hxC'⟩ := hxCC'
        rw [Set.mem_inter_iff, not_and_or] at hxss'
        rcases hxss' with hxs | hxs'
        · exact Or.inl (Or.inl ⟨hxC, hxs⟩)
        · exact Or.inr (Or.inl ⟨hxC', hxs'⟩)
      · obtain ⟨hxs, hxs'⟩ := hxss'
        rw [Set.mem_inter_iff, not_and_or] at hxCC'
        rcases hxCC' with hxC | hxC'
        · exact Or.inl (Or.inr ⟨hxs, hxC⟩)
        · exact Or.inr (Or.inr ⟨hxs', hxC'⟩)
    calc
      abs (mu.real (C ∩ C') - mu.real (s ∩ s')) ≤
          mu.real ((C ∩ C') ∆ (s ∩ s')) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hCmeas.inter hC'meas).nullMeasurableSet
          (hs.inter hs'meas).nullMeasurableSet
      _ ≤ mu.real ((C ∆ s) ∪ (C' ∆ s')) :=
        measureReal_mono hsub (by finiteness)
      _ ≤ mu.real (C ∆ s) + mu.real (C' ∆ s') :=
        measureReal_union_le _ _
  have hmix' : abs (mu.real (C ∩ C') - (mu.real C) ^ 2) < epsilon := by
    simpa only [Finset.mem_singleton, forall_const, C', pow_two] using
      hmixC C (by simp) C (by simp)
  have hsquares : abs ((mu.real C) ^ 2 - (mu.real s) ^ 2) ≤
      2 * mu.real (C ∆ s) := by
    have hCnn : 0 ≤ mu.real C := measureReal_nonneg
    have hsnn : 0 ≤ mu.real s := measureReal_nonneg
    have hCle : mu.real C ≤ 1 := measureReal_le_one
    have hsle : mu.real s ≤ 1 := measureReal_le_one
    calc
      abs (mu.real C ^ 2 - mu.real s ^ 2) =
          abs (mu.real C - mu.real s) * abs (mu.real C + mu.real s) := by
        rw [← abs_mul]
        ring_nf
      _ ≤ abs (mu.real C - mu.real s) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_of_nonneg (by positivity)]
        linarith
      _ ≤ mu.real (C ∆ s) * 2 :=
        mul_le_mul_of_nonneg_right hCs (by norm_num)
      _ = 2 * mu.real (C ∆ s) := by ring
  have htriangle :
      abs (mu.real (s ∩ s') - (mu.real s) ^ 2) ≤
        abs (mu.real (s ∩ s') - mu.real (C ∩ C')) +
          (abs (mu.real (C ∩ C') - (mu.real C) ^ 2) +
            abs ((mu.real C) ^ 2 - (mu.real s) ^ 2)) := by
    calc
      abs (mu.real (s ∩ s') - (mu.real s) ^ 2) ≤
          abs (mu.real (s ∩ s') - mu.real (C ∩ C')) +
            abs (mu.real (C ∩ C') - (mu.real s) ^ 2) :=
        abs_sub_le _ _ _
      _ ≤ abs (mu.real (s ∩ s') - mu.real (C ∩ C')) +
          (abs (mu.real (C ∩ C') - (mu.real C) ^ 2) +
            abs ((mu.real C) ^ 2 - (mu.real s) ^ 2)) := by
        linarith [abs_sub_le (mu.real (C ∩ C'))
          ((mu.real C) ^ 2) ((mu.real s) ^ 2)]
  have hCsd0 : 0 ≤ mu.real (C ∆ s) := measureReal_nonneg
  have hC'sd0 : 0 ≤ mu.real (C' ∆ s') := measureReal_nonneg
  change abs (mu.real (s ∩ s') - (mu.real s) ^ 2) < 5 * epsilon
  calc
    abs (mu.real (s ∩ s') - (mu.real s) ^ 2) ≤
        abs (mu.real (s ∩ s') - mu.real (C ∩ C')) +
          (abs (mu.real (C ∩ C') - (mu.real C) ^ 2) +
            abs ((mu.real C) ^ 2 - (mu.real s) ^ 2)) := htriangle
    _ ≤ (mu.real (C ∆ s) + mu.real (C' ∆ s')) +
          (epsilon + 2 * mu.real (C ∆ s)) := by
      apply add_le_add
      · rw [abs_sub_comm]
        exact hinter
      · exact add_le_add hmix'.le hsquares
    _ < 5 * epsilon := by linarith

end StatMech.FrontierB
