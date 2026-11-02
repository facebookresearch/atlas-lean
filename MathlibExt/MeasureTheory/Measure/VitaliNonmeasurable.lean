/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Vitali non-measurable set

Vitali's existence of a subset of `ℝ` that is not Lebesgue measurable,
via choice of representatives in `[0, 1]` for translation by rationals.
-/

@[expose] public section

namespace MeasureTheory

private def vitaliRel (x y : ℝ) : Prop := ∃ q : Rat, x - y = (q : ℝ)
private def vitaliSetoid : Setoid ℝ where
  r := vitaliRel
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := fun h => by
        obtain ⟨q, hq⟩ := h
        exact ⟨-q, by rw [Rat.cast_neg, ← hq]; ring⟩
      trans := fun h1 h2 => by
        obtain ⟨q1, h1⟩ := h1
        obtain ⟨q2, h2⟩ := h2
        exact ⟨q1 + q2, by rw [Rat.cast_add, ← h1, ← h2]; ring⟩ }
open Classical in
private noncomputable def vitaliChoice : Quotient vitaliSetoid → ℝ :=
  fun q =>
    if h : ∃ y, Quotient.mk vitaliSetoid y = q ∧ y ∈ Set.Icc (0 : ℝ) 1 then
      Classical.choose h
    else 0
private theorem vitaliChoice_spec (q : Quotient vitaliSetoid)
    (hq : ∃ y, Quotient.mk vitaliSetoid y = q ∧ y ∈ Set.Icc (0 : ℝ) 1) :
    Quotient.mk vitaliSetoid (vitaliChoice q) = q ∧ vitaliChoice q ∈ Set.Icc (0 : ℝ) 1 := by
  unfold vitaliChoice
  rw [dite_eq_left hq]
  exact Classical.choose_spec hq
private noncomputable def vitaliSet : Set ℝ :=
  { x | ∃ q, (∃ y, Quotient.mk vitaliSetoid y = q ∧ y ∈ Set.Icc (0 : ℝ) 1) ∧ vitaliChoice q = x }
private theorem vitaliSet_subset : vitaliSet ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := hx
  exact (vitaliChoice_spec q hq).2
private theorem vitaliSet_exists (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ v, v ∈ vitaliSet ∧ ∃ q : Rat, x - v = (q : ℝ) := by
  let q0 : Quotient vitaliSetoid := Quotient.mk vitaliSetoid x
  have hq0 : ∃ y, Quotient.mk vitaliSetoid y = q0 ∧ y ∈ Set.Icc (0 : ℝ) 1 := ⟨x, rfl, hx⟩
  have hv :
      Quotient.mk vitaliSetoid (vitaliChoice q0) = q0 ∧
        vitaliChoice q0 ∈ Set.Icc (0 : ℝ) 1 :=
    vitaliChoice_spec q0 hq0
  refine ⟨vitaliChoice q0, ⟨q0, hq0, rfl⟩, Quotient.exact hv.1.symm⟩
private theorem vitaliSet_eq_of_mem (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ vitaliSet) (hv₂ : v₂ ∈ vitaliSet)
    (q : Rat) (hq : v₁ - v₂ = (q : ℝ)) : v₁ = v₂ := by
  obtain ⟨q₁, hP₁, rfl⟩ := hv₁
  obtain ⟨q₂, hP₂, rfl⟩ := hv₂
  have h1 :
      Quotient.mk vitaliSetoid (vitaliChoice q₁) = q₁ ∧
        vitaliChoice q₁ ∈ Set.Icc (0 : ℝ) 1 :=
    vitaliChoice_spec q₁ hP₁
  have h2 :
      Quotient.mk vitaliSetoid (vitaliChoice q₂) = q₂ ∧
        vitaliChoice q₂ ∈ Set.Icc (0 : ℝ) 1 :=
    vitaliChoice_spec q₂ hP₂
  have hmk :
      Quotient.mk vitaliSetoid (vitaliChoice q₁) =
        Quotient.mk vitaliSetoid (vitaliChoice q₂) :=
    Quotient.sound (show vitaliSetoid.r _ _ from ⟨q, hq⟩)
  have hqq : q₁ = q₂ := h1.1.symm.trans (hmk.trans h2.1)
  rw [hqq]
private noncomputable def vitaliTranslate (a : ℝ) : Set ℝ := (fun y => -a + y) ⁻¹' vitaliSet
private theorem vitaliTranslate_measure (a : ℝ) :
    (volume : Measure ℝ) (vitaliTranslate a) = (volume : Measure ℝ) vitaliSet := by
  unfold vitaliTranslate
  apply measure_preimage_add
private theorem vitaliTranslate_null (a : ℝ)
    (hV : NullMeasurableSet vitaliSet (volume : Measure ℝ)) :
    NullMeasurableSet (vitaliTranslate a) (volume : Measure ℝ) := by
  have hfpres : MeasurePreserving (fun y => -a + y) (volume : Measure ℝ) (volume : Measure ℝ) := by
    apply measurePreserving_add_left
  exact hV.preimage hfpres.quasiMeasurePreserving
private theorem vitaliTranslate_disjoint (q₁ q₂ : Rat) (hne : q₁ ≠ q₂) :
    Disjoint (vitaliTranslate (q₁ : ℝ)) (vitaliTranslate (q₂ : ℝ)) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  have hv1 : (-(q₁ : ℝ) + y) ∈ vitaliSet := hy1
  have hv2 : (-(q₂ : ℝ) + y) ∈ vitaliSet := hy2
  have hsub : (-(q₁ : ℝ) + y) - (-(q₂ : ℝ) + y) = ((q₂ - q₁ : Rat) : ℝ) := by
    rw [Rat.cast_sub]
    ring
  have heq : (-(q₁ : ℝ) + y) = (-(q₂ : ℝ) + y) :=
    vitaliSet_eq_of_mem _ _ hv1 hv2 (q₂ - q₁) hsub
  have hcast0 : ((q₂ - q₁ : Rat) : ℝ) = 0 := by
    rw [← hsub]
    rw [heq]
    simp
  have hq0 : q₂ - q₁ = 0 := Rat.cast_eq_zero.mp hcast0
  have hqq : q₁ = q₂ := by linarith
  exact hne hqq
private def RatIcc : Type := { q : Rat // (-1 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (1 : ℝ) }
private def RatIoo : Type := { q : Rat // 0 < q ∧ q < 1 }
private instance : Countable RatIcc :=
  inferInstanceAs (Countable { q : Rat // (-1 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (1 : ℝ) })
private instance : Countable RatIoo :=
  inferInstanceAs (Countable { q : Rat // 0 < q ∧ q < 1 })
private noncomputable def FamIcc (q : RatIcc) : Set ℝ := vitaliTranslate (q.val : ℝ)
private noncomputable def FamIoo (q : RatIoo) : Set ℝ := vitaliTranslate (q.val : ℝ)
private theorem FamIcc_disjoint : Pairwise (Function.onFun Disjoint FamIcc) := by
  intro q₁ q₂ hne
  have hval : q₁.val ≠ q₂.val := fun h => hne (Subtype.ext h)
  exact vitaliTranslate_disjoint _ _ hval
private theorem FamIoo_disjoint : Pairwise (Function.onFun Disjoint FamIoo) := by
  intro q₁ q₂ hne
  have hval : q₁.val ≠ q₂.val := fun h => hne (Subtype.ext h)
  exact vitaliTranslate_disjoint _ _ hval
private theorem FamIcc_cover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ q, FamIcc q := by
  intro x hx
  obtain ⟨v, hvV, q, hq⟩ := vitaliSet_exists x hx
  have hvIcc : v ∈ Set.Icc (0 : ℝ) 1 := vitaliSet_subset hvV
  obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hx
  obtain ⟨hv0, hv1⟩ := Set.mem_Icc.mp hvIcc
  have hqlo : (-1 : ℝ) ≤ (q : ℝ) := by linarith
  have hqhi : (q : ℝ) ≤ (1 : ℝ) := by linarith
  have heq : -((q : ℝ)) + x = v := by rw [← hq]; ring
  have hmem : -((q : ℝ)) + x ∈ vitaliSet := by rw [heq]; exact hvV
  exact Set.mem_iUnion.mpr ⟨⟨q, hqlo, hqhi⟩, hmem⟩
private theorem FamIcc_bounded : ⋃ q, FamIcc q ⊆ Set.Icc (-1 : ℝ) 2 := by
  intro y hy
  obtain ⟨q, hqy⟩ := Set.mem_iUnion.mp hy
  have hvIcc : -((q.val : ℝ)) + y ∈ Set.Icc (0 : ℝ) 1 := vitaliSet_subset hqy
  obtain ⟨h0, h1⟩ := Set.mem_Icc.mp hvIcc
  obtain ⟨hqlo, hqhi⟩ := q.property
  rw [Set.mem_Icc]
  constructor <;> linarith
private theorem FamIoo_bounded : ⋃ q, FamIoo q ⊆ Set.Icc (-1 : ℝ) 2 := by
  intro y hy
  obtain ⟨q, hqy⟩ := Set.mem_iUnion.mp hy
  have hvIcc : -((q.val : ℝ)) + y ∈ Set.Icc (0 : ℝ) 1 := vitaliSet_subset hqy
  obtain ⟨h0, h1⟩ := Set.mem_Icc.mp hvIcc
  have h0q : (0 : ℝ) < (q.val : ℝ) := by exact_mod_cast q.property.1
  have hq1 : (q.val : ℝ) < (1 : ℝ) := by exact_mod_cast q.property.2
  rw [Set.mem_Icc]
  constructor <;> linarith
private theorem measure_Icc01 : (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) = 1 := by simp
private theorem measure_Icc12 : (volume : Measure ℝ) (Set.Icc (-1 : ℝ) 2) = 3 := by
  rw [Real.volume_Icc]; norm_num
private theorem RatIoo_infinite : (Set.Ioo (0 : Rat) 1).Infinite :=
  Set.Ioo_infinite (by linarith)
private instance : Infinite RatIoo := RatIoo_infinite.to_subtype
/--
**Vitali's theorem.** There exists a subset of $\mathbb{R}$ that is not Lebesgue measurable.

Source: G. Vitali, Sul problema della misura dei gruppi di punti di una retta, Tipografia Gamberini
e Parmeggiani, Bologna (1905). Here `NullMeasurableSet` w.r.t. `volume` is the
Lebesgue-measurability notion, i.e. measurability for the completion of Lebesgue measure.
-/
theorem vitali_nonmeasurable :
    ∃ s : Set ℝ, ¬ NullMeasurableSet s (volume : Measure ℝ)
  := by
  use vitaliSet
  intro hV
  by_cases h0 : (volume : Measure ℝ) vitaliSet = 0
  · have hNull : ∀ q : RatIcc, NullMeasurableSet (FamIcc q) (volume : Measure ℝ) :=
      fun q => vitaliTranslate_null _ hV
    have hDisj : Pairwise (Function.onFun (AEDisjoint (volume : Measure ℝ)) FamIcc) := by
      intro q₁ q₂ hne
      exact Disjoint.aedisjoint (FamIcc_disjoint hne)
    have hUnion : (volume : Measure ℝ) (⋃ q, FamIcc q) = ∑' q, (volume : Measure ℝ) (FamIcc q) :=
      measure_iUnion₀ hDisj hNull
    have hEach : ∀ q : RatIcc, (volume : Measure ℝ) (FamIcc q) = 0 := fun q => by
      have hm :
          (volume : Measure ℝ) (vitaliTranslate (q.val : ℝ)) =
            (volume : Measure ℝ) vitaliSet :=
        vitaliTranslate_measure _
      rw [h0] at hm
      exact hm
    have hSum : (∑' q : RatIcc, (volume : Measure ℝ) (FamIcc q)) = 0 := by
      rw [tsum_congr hEach]
      exact tsum_zero
    have hUZ : (volume : Measure ℝ) (⋃ q, FamIcc q) = 0 := hUnion.trans hSum
    have hMono :
        (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) ≤
          (volume : Measure ℝ) (⋃ q, FamIcc q) := by
      apply measure_mono
      exact FamIcc_cover
    rw [measure_Icc01, hUZ] at hMono
    have h10 : (1 : ENNReal) = 0 := le_antisymm hMono bot_le
    exact one_ne_zero h10
  · have hNull : ∀ q : RatIoo, NullMeasurableSet (FamIoo q) (volume : Measure ℝ) :=
      fun q => vitaliTranslate_null _ hV
    have hDisj : Pairwise (Function.onFun (AEDisjoint (volume : Measure ℝ)) FamIoo) := by
      intro q₁ q₂ hne
      exact Disjoint.aedisjoint (FamIoo_disjoint hne)
    have hUnion : (volume : Measure ℝ) (⋃ q, FamIoo q) = ∑' q, (volume : Measure ℝ) (FamIoo q) :=
      measure_iUnion₀ hDisj hNull
    have hEach : ∀ q : RatIoo, (volume : Measure ℝ) (FamIoo q) = (volume : Measure ℝ) vitaliSet :=
      fun q => vitaliTranslate_measure _
    have hSumEq :
        (∑' q : RatIoo, (volume : Measure ℝ) (FamIoo q)) =
          ∑' _ : RatIoo, (volume : Measure ℝ) vitaliSet :=
      tsum_congr hEach
    have hTop : (∑' _ : RatIoo, (volume : Measure ℝ) vitaliSet) = ⊤ :=
      ENNReal.tsum_const_eq_top_of_ne_zero h0
    have hUT : (volume : Measure ℝ) (⋃ q, FamIoo q) = ⊤ :=
      hUnion.trans (hSumEq.trans hTop)
    have hMono :
        (volume : Measure ℝ) (⋃ q, FamIoo q) ≤
          (volume : Measure ℝ) (Set.Icc (-1 : ℝ) 2) := by
      apply measure_mono
      exact FamIoo_bounded
    rw [measure_Icc12, hUT] at hMono
    have h3T : (3 : ENNReal) = ⊤ := le_antisymm le_top hMono
    have h3ne : (3 : ENNReal) ≠ ⊤ := by simp
    exact h3ne h3T

end MeasureTheory
