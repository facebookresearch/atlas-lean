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
import Code.Inequalities.IncreasingEvent
import Code.Universality.Defs

open Set MeasureTheory SimpleGraph

namespace StatMech

namespace RSW

namespace Strip

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.Universality













theorem connectedWithin_mono_set {d : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {S T : Set (Site d)} (hST : S ⊆ T) {x y : S}
    (h : ConnectedWithin d ω S x y) :
    ConnectedWithin d ω T ⟨(x : Site d), hST x.2⟩ ⟨(y : Site d), hST y.2⟩ := by
  let f : (openSubgraph d ω).induce S →g (openSubgraph d ω).induce T :=
    { toFun := fun z => ⟨(z : Site d), hST z.2⟩
      map_rel' := fun {a b} hab => hab }
  exact h.map f


theorem connectedWithin_union_left {d : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    (S T : Set (Site d)) {x y : Site d} (hx : x ∈ S) (hy : y ∈ S)
    (h : ConnectedWithin d ω S ⟨x, hx⟩ ⟨y, hy⟩) :
    ConnectedWithin d ω (S ∪ T) ⟨x, Or.inl hx⟩ ⟨y, Or.inl hy⟩ :=
  connectedWithin_mono_set ω Set.subset_union_left h


theorem connectedWithin_union_right {d : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    (S T : Set (Site d)) {x y : Site d} (hx : x ∈ T) (hy : y ∈ T)
    (h : ConnectedWithin d ω T ⟨x, hx⟩ ⟨y, hy⟩) :
    ConnectedWithin d ω (S ∪ T) ⟨x, Or.inr hx⟩ ⟨y, Or.inr hy⟩ :=
  connectedWithin_mono_set ω Set.subset_union_right h





theorem connectedWithin_glue {d : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    (S T : Set (Site d)) {x z y : Site d}
    (hxS : x ∈ S) (hzS : z ∈ S) (hzT : z ∈ T) (hyT : y ∈ T)
    (h1 : ConnectedWithin d ω S ⟨x, hxS⟩ ⟨z, hzS⟩)
    (h2 : ConnectedWithin d ω T ⟨z, hzT⟩ ⟨y, hyT⟩) :
    ConnectedWithin d ω (S ∪ T) ⟨x, Or.inl hxS⟩ ⟨y, Or.inr hyT⟩ :=
  (connectedWithin_union_left ω S T hxS hzS h1).trans
    (connectedWithin_union_right ω S T hzT hyT h2)









theorem rect_subset_of_right {a m b c d : ℤ} (hmb : m ≤ b) :
    rect a m c d ⊆ rect a b c d :=
  fun _ hx => ⟨hx.1, le_trans hx.2.1 hmb, hx.2.2.1, hx.2.2.2⟩


theorem rect_subset_of_left {a m b c d : ℤ} (ham : a ≤ m) :
    rect m b c d ⊆ rect a b c d :=
  fun _ hx => ⟨le_trans ham hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩


theorem rect_subset_of_top {a b c m d : ℤ} (hmd : m ≤ d) :
    rect a b c m ⊆ rect a b c d :=
  fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.1, le_trans hx.2.2.2 hmd⟩


theorem rect_subset_of_bottom {a b c m d : ℤ} (hcm : c ≤ m) :
    rect a b m d ⊆ rect a b c d :=
  fun _ hx => ⟨hx.1, hx.2.1, le_trans hcm hx.2.2.1, hx.2.2.2⟩



theorem rect_union_horiz {a m b c d : ℤ} (ham : a ≤ m) (hmb : m ≤ b) :
    rect a m c d ∪ rect m b c d = rect a b c d := by
  ext x
  simp only [mem_rect, Set.mem_union]
  constructor
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, le_trans h2 hmb, h3, h4⟩
    · exact ⟨le_trans ham h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total (x 0) m with h | h
    · exact Or.inl ⟨h1, h, h3, h4⟩
    · exact Or.inr ⟨h, h2, h3, h4⟩



theorem rect_union_vert {a b c m d : ℤ} (hcm : c ≤ m) (hmd : m ≤ d) :
    rect a b c m ∪ rect a b m d = rect a b c d := by
  ext x
  simp only [mem_rect, Set.mem_union]
  constructor
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, h2, h3, le_trans h4 hmd⟩
    · exact ⟨h1, h2, le_trans hcm h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total (x 1) m with h | h
    · exact Or.inl ⟨h1, h2, h3, h⟩
    · exact Or.inr ⟨h1, h2, h, h4⟩



theorem mem_shared_column {a m b c d : ℤ} (ham : a ≤ m) (hmb : m ≤ b)
    {z : Site 2} (hz0 : z 0 = m) (hzc : c ≤ z 1) (hzd : z 1 ≤ d) :
    z ∈ rightSide a m c d ∧ z ∈ leftSide m b c d :=
  ⟨⟨⟨ham.trans_eq hz0.symm, hz0.le, hzc, hzd⟩, hz0⟩,
   ⟨⟨hz0.ge, hz0.le.trans hmb, hzc, hzd⟩, hz0⟩⟩


















theorem horizontalCrossing_glue {ω : ConfigSpace (Sym2 (Site 2))} {a m b c d : ℤ}
    (ham : a ≤ m) (hmb : m ≤ b)
    
    {xL : Site 2} (hxL : xL ∈ leftSide a m c d)
    {p : Site 2} (hp : p ∈ rightSide a m c d)
    (hc1 : ConnectedWithin 2 ω (rect a m c d)
      ⟨xL, leftSide_subset hxL⟩ ⟨p, rightSide_subset hp⟩)
    
    {q : Site 2} (hq : q ∈ leftSide m b c d)
    {yR : Site 2} (hyR : yR ∈ rightSide m b c d)
    (hc2 : ConnectedWithin 2 ω (rect m b c d)
      ⟨q, leftSide_subset hq⟩ ⟨yR, rightSide_subset hyR⟩)
    
    (hglue : ConnectedWithin 2 ω (rect a b c d)
      ⟨p, rect_subset_of_right hmb (rightSide_subset hp)⟩
      ⟨q, rect_subset_of_left ham (leftSide_subset hq)⟩) :
    HorizontalCrossing ω a b c d := by
  have hxLab : xL ∈ leftSide a b c d := ⟨rect_subset_of_right hmb hxL.1, hxL.2⟩
  have hyRab : yR ∈ rightSide a b c d := ⟨rect_subset_of_left ham hyR.1, hyR.2⟩
  refine ⟨⟨xL, hxLab⟩, ⟨yR, hyRab⟩, ?_⟩
  have e1 := connectedWithin_mono_set ω (rect_subset_of_right hmb) hc1
  have e2 := connectedWithin_mono_set ω (rect_subset_of_left ham) hc2
  exact (e1.trans hglue).trans e2






theorem horizontalCrossing_glue_of_meet {ω : ConfigSpace (Sym2 (Site 2))}
    {a m b c d : ℤ} (ham : a ≤ m) (hmb : m ≤ b)
    {xL : Site 2} (hxL : xL ∈ leftSide a m c d)
    {z : Site 2} (hz0 : z 0 = m) (hzc : c ≤ z 1) (hzd : z 1 ≤ d)
    (hc1 : ConnectedWithin 2 ω (rect a m c d)
      ⟨xL, leftSide_subset hxL⟩
      ⟨z, rightSide_subset (mem_shared_column ham hmb hz0 hzc hzd).1⟩)
    {yR : Site 2} (hyR : yR ∈ rightSide m b c d)
    (hc2 : ConnectedWithin 2 ω (rect m b c d)
      ⟨z, leftSide_subset (mem_shared_column ham hmb hz0 hzc hzd).2⟩
      ⟨yR, rightSide_subset hyR⟩) :
    HorizontalCrossing ω a b c d := by
  obtain ⟨hzR1, hzL2⟩ := mem_shared_column ham hmb hz0 hzc hzd
  refine horizontalCrossing_glue ham hmb hxL hzR1 hc1 hzL2 hyR hc2 ?_
  
  exact connectedWithin_refl ω (rect a b c d) _



theorem mem_shared_row {a b c m d : ℤ} (hcm : c ≤ m) (hmd : m ≤ d)
    {z : Site 2} (hz1 : z 1 = m) (hza : a ≤ z 0) (hzb : z 0 ≤ b) :
    z ∈ topSide a b c m ∧ z ∈ bottomSide a b m d :=
  ⟨⟨⟨hza, hzb, hcm.trans_eq hz1.symm, hz1.le⟩, hz1⟩,
   ⟨⟨hza, hzb, hz1.ge, hz1.le.trans hmd⟩, hz1⟩⟩






theorem verticalCrossing_glue {ω : ConfigSpace (Sym2 (Site 2))} {a b c m d : ℤ}
    (hcm : c ≤ m) (hmd : m ≤ d)
    {xB : Site 2} (hxB : xB ∈ bottomSide a b c m)
    {p : Site 2} (hp : p ∈ topSide a b c m)
    (hc1 : ConnectedWithin 2 ω (rect a b c m)
      ⟨xB, bottomSide_subset hxB⟩ ⟨p, topSide_subset hp⟩)
    {q : Site 2} (hq : q ∈ bottomSide a b m d)
    {yT : Site 2} (hyT : yT ∈ topSide a b m d)
    (hc2 : ConnectedWithin 2 ω (rect a b m d)
      ⟨q, bottomSide_subset hq⟩ ⟨yT, topSide_subset hyT⟩)
    (hglue : ConnectedWithin 2 ω (rect a b c d)
      ⟨p, rect_subset_of_top hmd (topSide_subset hp)⟩
      ⟨q, rect_subset_of_bottom hcm (bottomSide_subset hq)⟩) :
    VerticalCrossing ω a b c d := by
  have hxBab : xB ∈ bottomSide a b c d := ⟨rect_subset_of_top hmd hxB.1, hxB.2⟩
  have hyTab : yT ∈ topSide a b c d := ⟨rect_subset_of_bottom hcm hyT.1, hyT.2⟩
  refine ⟨⟨xB, hxBab⟩, ⟨yT, hyTab⟩, ?_⟩
  have e1 := connectedWithin_mono_set ω (rect_subset_of_top hmd) hc1
  have e2 := connectedWithin_mono_set ω (rect_subset_of_bottom hcm) hc2
  exact (e1.trans hglue).trans e2


theorem verticalCrossing_glue_of_meet {ω : ConfigSpace (Sym2 (Site 2))}
    {a b c m d : ℤ} (hcm : c ≤ m) (hmd : m ≤ d)
    {xB : Site 2} (hxB : xB ∈ bottomSide a b c m)
    {z : Site 2} (hz1 : z 1 = m) (hza : a ≤ z 0) (hzb : z 0 ≤ b)
    (hc1 : ConnectedWithin 2 ω (rect a b c m)
      ⟨xB, bottomSide_subset hxB⟩
      ⟨z, topSide_subset (mem_shared_row hcm hmd hz1 hza hzb).1⟩)
    {yT : Site 2} (hyT : yT ∈ topSide a b m d)
    (hc2 : ConnectedWithin 2 ω (rect a b m d)
      ⟨z, bottomSide_subset (mem_shared_row hcm hmd hz1 hza hzb).2⟩
      ⟨yT, topSide_subset hyT⟩) :
    VerticalCrossing ω a b c d := by
  obtain ⟨hzT1, hzB2⟩ := mem_shared_row hcm hmd hz1 hza hzb
  refine verticalCrossing_glue hcm hmd hxB hzT1 hc1 hzB2 hyT hc2 ?_
  exact connectedWithin_refl ω (rect a b c d) _








theorem horizontalCrossingEvent_isIncreasing (a b c d : ℤ) :
    IsIncreasing (horizontalCrossingEvent a b c d) :=
  fun _ _ h hω => horizontalCrossingEvent_increasing h hω


theorem verticalCrossingEvent_isIncreasing (a b c d : ℤ) :
    IsIncreasing (verticalCrossingEvent a b c d) :=
  fun _ _ h hω => verticalCrossingEvent_increasing h hω















theorem measureReal_glue_ge_mul {E : Type*} (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] (hpa : PositivelyAssociated μ)
    {A B C : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hsub : A ∩ B ⊆ C) :
    μ.real A * μ.real B ≤ μ.real C :=
  (hpa A B hA hB).trans (measureReal_mono hsub)






theorem measureReal_crossing_product_le {E : Type*} (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] (hpa : PositivelyAssociated μ)
    {A C : Set (ConfigSpace E)} (hA : IsIncreasing A) (hsub : A ∩ A ⊆ C) :
    μ.real A * μ.real A ≤ μ.real C :=
  measureReal_glue_ge_mul μ hpa hA hA hsub
















def LeftHalfCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a m c d : ℤ) (z : Site 2)
    (hz : z ∈ rect a m c d) : Prop :=
  ∃ xL : leftSide a m c d,
    ConnectedWithin 2 ω (rect a m c d) ⟨xL, leftSide_subset xL.2⟩ ⟨z, hz⟩




def RightHalfCrossing (ω : ConfigSpace (Sym2 (Site 2))) (m b c d : ℤ) (z : Site 2)
    (hz : z ∈ rect m b c d) : Prop :=
  ∃ yR : rightSide m b c d,
    ConnectedWithin 2 ω (rect m b c d) ⟨z, hz⟩ ⟨yR, rightSide_subset yR.2⟩


def leftHalfCrossingEvent (a m c d : ℤ) (z : Site 2) (hz : z ∈ rect a m c d) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | LeftHalfCrossing ω a m c d z hz}


def rightHalfCrossingEvent (m b c d : ℤ) (z : Site 2) (hz : z ∈ rect m b c d) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | RightHalfCrossing ω m b c d z hz}


theorem leftHalfCrossingEvent_isIncreasing (a m c d : ℤ) (z : Site 2)
    (hz : z ∈ rect a m c d) :
    IsIncreasing (leftHalfCrossingEvent a m c d z hz) := by
  intro ω ω' hωω' hω
  obtain ⟨xL, hc⟩ := hω
  exact ⟨xL, StatMech.TwoDim.connectedWithin_mono hωω' hc⟩


theorem rightHalfCrossingEvent_isIncreasing (m b c d : ℤ) (z : Site 2)
    (hz : z ∈ rect m b c d) :
    IsIncreasing (rightHalfCrossingEvent m b c d z hz) := by
  intro ω ω' hωω' hω
  obtain ⟨yR, hc⟩ := hω
  exact ⟨yR, StatMech.TwoDim.connectedWithin_mono hωω' hc⟩








theorem halfCrossing_glue_subset {a m b c d : ℤ} (ham : a ≤ m) (hmb : m ≤ b)
    {z : Site 2} (hz0 : z 0 = m) (hzc : c ≤ z 1) (hzd : z 1 ≤ d) :
    leftHalfCrossingEvent a m c d z
        (rightSide_subset (mem_shared_column ham hmb hz0 hzc hzd).1)
      ∩ rightHalfCrossingEvent m b c d z
        (leftSide_subset (mem_shared_column ham hmb hz0 hzc hzd).2)
      ⊆ horizontalCrossingEvent a b c d := by
  rintro ω ⟨⟨xL, hc1⟩, ⟨yR, hc2⟩⟩
  obtain ⟨hzR1, hzL2⟩ := mem_shared_column ham hmb hz0 hzc hzd
  exact horizontalCrossing_glue_of_meet ham hmb xL.2 hz0 hzc hzd hc1 yR.2 hc2







theorem measureReal_horizontalCrossing_ge_halves {a m b c d : ℤ}
    (ham : a ≤ m) (hmb : m ≤ b) {z : Site 2} (hz0 : z 0 = m) (hzc : c ≤ z 1)
    (hzd : z 1 ≤ d) (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsFiniteMeasure μ]
    (hpa : PositivelyAssociated μ) :
    μ.real (leftHalfCrossingEvent a m c d z
          (rightSide_subset (mem_shared_column ham hmb hz0 hzc hzd).1))
        * μ.real (rightHalfCrossingEvent m b c d z
          (leftSide_subset (mem_shared_column ham hmb hz0 hzc hzd).2))
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  measureReal_glue_ge_mul μ hpa
    (leftHalfCrossingEvent_isIncreasing a m c d z _)
    (rightHalfCrossingEvent_isIncreasing m b c d z _)
    (halfCrossing_glue_subset ham hmb hz0 hzc hzd)
















theorem measureReal_chain_ge_prod {ι : Type*} {E : Type*}
    (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (s : Finset ι)
    {A : ι → Set (ConfigSpace E)} (hA : ∀ i, IsIncreasing (A i))
    {C : Set (ConfigSpace E)} (hsub : (⋂ i ∈ s, A i) ⊆ C) :
    (∏ i ∈ s, μ.real (A i)) ≤ μ.real C := by
  classical
  induction s using Finset.induction generalizing C with
  | empty =>
      
      simp only [Finset.prod_empty]
      have huniv : (Set.univ : Set (ConfigSpace E)) ⊆ C := by
        simpa using hsub
      have hC : C = Set.univ := Set.eq_univ_of_univ_subset huniv
      subst hC
      simp [measureReal_def]
  | insert i s hi ih =>
      
      rw [Finset.prod_insert hi]
      
      have hInterInc : IsIncreasing (⋂ j ∈ s, A j) := by
        apply isIncreasing_iInter
        intro j
        apply isIncreasing_iInter
        intro _
        exact hA j
      
      have hstep := ih (C := ⋂ j ∈ s, A j) (le_refl _)
      
      have hincl : A i ∩ (⋂ j ∈ s, A j) ⊆ C := by
        refine subset_trans ?_ hsub
        intro ω hω
        rw [Set.mem_iInter₂]
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact hω.1
        · exact (Set.mem_iInter₂.mp hω.2) j hjs
      calc μ.real (A i) * (∏ j ∈ s, μ.real (A j))
          ≤ μ.real (A i) * μ.real (⋂ j ∈ s, A j) := by
            apply mul_le_mul_of_nonneg_left hstep (measureReal_nonneg)
        _ ≤ μ.real (A i ∩ (⋂ j ∈ s, A j)) := hpa _ _ (hA i) hInterInc
        _ ≤ μ.real C := measureReal_mono hincl

end Strip

end RSW

end StatMech
