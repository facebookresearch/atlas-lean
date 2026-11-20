/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Lattice.Clusters
import Code.TwoDim.Crossings
import Code.RSW.Defs
import Code.RSW.Strip
import Code.Inequalities.IncreasingEvent
import Code.Universality.Defs

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip














theorem PositivelyAssociated.decreasing {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : Set (ConfigSpace E)} (hA : IsDecreasing A) (hB : IsDecreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
  
  have hfkg := hpa Aᶜ Bᶜ hA.compl hB.compl
  have hca : μ.real Aᶜ = 1 - μ.real A := by rw [measureReal_compl hAm, probReal_univ]
  have hcb : μ.real Bᶜ = 1 - μ.real B := by rw [measureReal_compl hBm, probReal_univ]
  have hcum : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real (A ∪ B) := by
    rw [← Set.compl_union, measureReal_compl (hAm.union hBm), probReal_univ]
  rw [hca, hcb, hcum] at hfkg
  
  have hie : μ.real (A ∪ B) + μ.real (A ∩ B) = μ.real A + μ.real B :=
    measureReal_union_add_inter hBm
  nlinarith [hfkg, hie]






theorem complUnion_fkg_bound {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (1 - μ.real A) * (1 - μ.real B) ≤ 1 - μ.real (A ∪ B) := by
  have hdec := hpa.decreasing μ hA.compl hB.compl hAm.compl hBm.compl
  have hca : μ.real Aᶜ = 1 - μ.real A := by rw [measureReal_compl hAm, probReal_univ]
  have hcb : μ.real Bᶜ = 1 - μ.real B := by rw [measureReal_compl hBm, probReal_univ]
  have hcum : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real (A ∪ B) := by
    rw [← Set.compl_union, measureReal_compl (hAm.union hBm), probReal_univ]
  rw [hca, hcb, hcum] at hdec
  exact hdec





theorem sqrt_trick_max_real {a b s : ℝ} (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : (1 - a) * (1 - b) ≤ 1 - s) :
    1 - Real.sqrt (1 - s) ≤ max a b := by
  rcases le_total a b with hab | hba
  · 
    have h1b : (0 : ℝ) ≤ 1 - b := by linarith
    have hbb : (1 - b) ^ 2 ≤ 1 - s := by nlinarith
    have hsq : Real.sqrt ((1 - b) ^ 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt hbb
    rw [Real.sqrt_sq h1b] at hsq
    rw [max_eq_right hab]; linarith
  · have h1a : (0 : ℝ) ≤ 1 - a := by linarith
    have haa : (1 - a) ^ 2 ≤ 1 - s := by nlinarith
    have hsq : Real.sqrt ((1 - a) ^ 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt haa
    rw [Real.sqrt_sq h1a] at hsq
    rw [max_eq_left hba]; linarith









theorem rsw_sqrt_trick {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ max (μ.real A) (μ.real B) :=
  sqrt_trick_max_real measureReal_le_one measureReal_le_one
    (complUnion_fkg_bound μ hpa hA hB hAm hBm)





theorem rsw_sqrt_trick_eq {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hAB : μ.real A = μ.real B) :
    1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ μ.real A := by
  have := rsw_sqrt_trick μ hpa hA hB hAm hBm
  rwa [← hAB, max_self] at this
























theorem hv_glue {ω : ConfigSpace (Sym2 (Site 2))} {a m m' b c d : ℤ}
    (ham : a ≤ m) (hm'b : m' ≤ b)
    {xL : Site 2} (hxL : xL ∈ leftSide a m' c d)
    {p : Site 2} (hpO : p ∈ rect m m' c d) (hpL : p ∈ rect a m' c d)
    (hc1 : ConnectedWithin 2 ω (rect a m' c d) ⟨xL, leftSide_subset hxL⟩ ⟨p, hpL⟩)
    {q : Site 2} (hqO : q ∈ rect m m' c d)
    (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨p, hpO⟩ ⟨q, hqO⟩)
    {yR : Site 2} (hyR : yR ∈ rightSide m b c d) (hqR : q ∈ rect m b c d)
    (hc2 : ConnectedWithin 2 ω (rect m b c d) ⟨q, hqR⟩ ⟨yR, rightSide_subset hyR⟩) :
    HorizontalCrossing ω a b c d := by
  
  have hsubL : rect a m' c d ⊆ rect a b c d := rect_subset_of_right hm'b
  have hsubO : rect m m' c d ⊆ rect a b c d := fun x hx =>
    ⟨le_trans ham hx.1, le_trans hx.2.1 hm'b, hx.2.2.1, hx.2.2.2⟩
  have hsubR : rect m b c d ⊆ rect a b c d := rect_subset_of_left ham
  have hxLab : xL ∈ leftSide a b c d := ⟨hsubL (leftSide_subset hxL), hxL.2⟩
  have hyRab : yR ∈ rightSide a b c d := ⟨hsubR (rightSide_subset hyR), hyR.2⟩
  refine ⟨⟨xL, hxLab⟩, ⟨yR, hyRab⟩, ?_⟩
  
  have e1 := connectedWithin_mono_set ω hsubL hc1
  have eV := connectedWithin_mono_set ω hsubO hcV
  have e2 := connectedWithin_mono_set ω hsubR hc2
  exact (e1.trans eV).trans e2














def OverlapConnection (ω : ConfigSpace (Sym2 (Site 2))) (m m' c d : ℤ)
    (p q : Site 2) (hp : p ∈ rect m m' c d) (hq : q ∈ rect m m' c d) : Prop :=
  ConnectedWithin 2 ω (rect m m' c d) ⟨p, hp⟩ ⟨q, hq⟩


def overlapConnectionEvent (m m' c d : ℤ) (p q : Site 2)
    (hp : p ∈ rect m m' c d) (hq : q ∈ rect m m' c d) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | OverlapConnection ω m m' c d p q hp hq}



theorem overlapConnectionEvent_isIncreasing (m m' c d : ℤ) (p q : Site 2)
    (hp : p ∈ rect m m' c d) (hq : q ∈ rect m m' c d) :
    IsIncreasing (overlapConnectionEvent m m' c d p q hp hq) := by
  intro ω ω' hωω' hω
  exact StatMech.TwoDim.connectedWithin_mono hωω' hω













theorem hvHalf_glue_subset {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m')
    (hm'b : m' ≤ b) {p q : Site 2}
    (hpO : p ∈ rect m m' c d) (hqO : q ∈ rect m m' c d)
    (hpL : p ∈ rect a m' c d) (hqR : q ∈ rect m b c d) :
    leftHalfCrossingEvent a m' c d p hpL
        ∩ overlapConnectionEvent m m' c d p q hpO hqO
        ∩ rightHalfCrossingEvent m b c d q hqR
      ⊆ horizontalCrossingEvent a b c d := by
  
  have _hoverlap : m ≤ m' := hmm'
  rintro ω ⟨⟨⟨xL, hc1⟩, hcV⟩, ⟨yR, hc2⟩⟩
  exact hv_glue ham hm'b xL.2 hpO hpL hc1 hqO hcV yR.2 hqR hc2













theorem rsw_strip_glue (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    {p q : Site 2} (hpO : p ∈ rect m m' c d) (hqO : q ∈ rect m m' c d)
    (hpL : p ∈ rect a m' c d) (hqR : q ∈ rect m b c d) :
    μ.real (leftHalfCrossingEvent a m' c d p hpL)
        * μ.real (overlapConnectionEvent m m' c d p q hpO hqO)
        * μ.real (rightHalfCrossingEvent m b c d q hqR)
      ≤ μ.real (horizontalCrossingEvent a b c d) := by
  set A := leftHalfCrossingEvent a m' c d p hpL
  set B := overlapConnectionEvent m m' c d p q hpO hqO
  set C := rightHalfCrossingEvent m b c d q hqR
  have hA : IsIncreasing A := leftHalfCrossingEvent_isIncreasing a m' c d p hpL
  have hB : IsIncreasing B := overlapConnectionEvent_isIncreasing m m' c d p q hpO hqO
  have hC : IsIncreasing C := rightHalfCrossingEvent_isIncreasing m b c d q hqR
  have hsub : A ∩ B ∩ C ⊆ horizontalCrossingEvent a b c d :=
    hvHalf_glue_subset ham hmm' hm'b hpO hqO hpL hqR
  
  have h1 : μ.real A * μ.real B ≤ μ.real (A ∩ B) := hpa A B hA hB
  have h2 : μ.real (A ∩ B) * μ.real C ≤ μ.real (A ∩ B ∩ C) :=
    hpa (A ∩ B) C (hA.inter hB) hC
  have hnn : (0 : ℝ) ≤ μ.real C := measureReal_nonneg
  calc μ.real A * μ.real B * μ.real C
      ≤ μ.real (A ∩ B) * μ.real C := mul_le_mul_of_nonneg_right h1 hnn
    _ ≤ μ.real (A ∩ B ∩ C) := h2
    _ ≤ μ.real (horizontalCrossingEvent a b c d) := measureReal_mono hsub






















def HVIntersectionProperty (ω : ConfigSpace (Sym2 (Site 2))) (a m m' b c d : ℤ) : Prop :=
  HorizontalCrossing ω a m' c d → VerticalCrossing ω m m' c d →
    HorizontalCrossing ω m b c d → HorizontalCrossing ω a b c d














theorem rsw_strip_glue_of_intersection (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ}
    (hint : ∀ ω, HVIntersectionProperty ω a m m' b c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) := by
  set A := horizontalCrossingEvent a m' c d
  set B := verticalCrossingEvent m m' c d
  set C := horizontalCrossingEvent m b c d
  have hA : IsIncreasing A := horizontalCrossingEvent_isIncreasing a m' c d
  have hB : IsIncreasing B := verticalCrossingEvent_isIncreasing m m' c d
  have hC : IsIncreasing C := horizontalCrossingEvent_isIncreasing m b c d
  have hsub : A ∩ B ∩ C ⊆ horizontalCrossingEvent a b c d := by
    rintro ω ⟨⟨hAω, hBω⟩, hCω⟩
    exact hint ω hAω hBω hCω
  have h1 : μ.real A * μ.real B ≤ μ.real (A ∩ B) := hpa A B hA hB
  have h2 : μ.real (A ∩ B) * μ.real C ≤ μ.real (A ∩ B ∩ C) :=
    hpa (A ∩ B) C (hA.inter hB) hC
  have hnn : (0 : ℝ) ≤ μ.real C := measureReal_nonneg
  calc μ.real A * μ.real B * μ.real C
      ≤ μ.real (A ∩ B) * μ.real C := mul_le_mul_of_nonneg_right h1 hnn
    _ ≤ μ.real (A ∩ B ∩ C) := h2
    _ ≤ μ.real (horizontalCrossingEvent a b c d) := measureReal_mono hsub

end Universality

end StatMech
