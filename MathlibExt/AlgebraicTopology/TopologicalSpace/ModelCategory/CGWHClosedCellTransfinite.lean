/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Colimits
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

import MathlibExt.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Injective transfinite colimits in CGWH

This file proves that the inclusion of compactly generated weak Hausdorff
spaces into compactly generated spaces preserves well-order-continuous
colimits whose successor maps are injective.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace CGWH

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem compactlyGeneratedColimit_isWeakHausdorff_of_injective
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (F : I ⥤ CGWH.{u, v})
    (hF : ∀ ⦃a b : I⦄ (f : a ⟶ b), Function.Injective
      (cgwhToCompactlyGenerated.map (F.map f)).hom) :
    UWeakHausdorffSpace.{u}
      ((Limits.colimit (F ⋙ cgwhToCompactlyGenerated) :
        CompactlyGenerated.{u, v}) : Type v) := by
  let D := F ⋙ cgwhToCompactlyGenerated
  let c := Limits.colimit.cocone D
  let hc := Limits.colimit.isColimit D
  let _ : BraidedCategory CompactlyGenerated.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : IsSifted I := IsFiltered.isSifted
  let c₂ := c.tensor c
  let hc₂ : IsColimit c₂ := hc.tensor hc
  let k := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  let L := c.pt
  let cTop := k.mapCocone c₂
  let hcTop : IsColimit cTop :=
    isColimitOfPreserves k hc₂
  let fstL : cTop.pt ⟶ k.obj L := by
    change k.obj (L ⊗ L) ⟶ k.obj L
    exact k.map (CartesianMonoidalCategory.fst L L)
  let sndL : cTop.pt ⟶ k.obj L := by
    change k.obj (L ⊗ L) ⟶ k.obj L
    exact k.map (CartesianMonoidalCategory.snd L L)
  let diagonal : Set cTop.pt := {p | fstL p = sndL p}
  rw [CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal]
  change IsClosed diagonal
  rw [TopCat.isClosed_iff_of_isColimit cTop hcTop diagonal]
  intro a
  let _ : PreservesColimitsOfShape I (forget CompactlyGenerated) := by
    change PreservesColimitsOfShape I
      (CompactlyGenerated.compactlyGeneratedToTop ⋙ forget TopCat)
    infer_instance
  have hinj : Function.Injective (c.ι.app a).hom :=
    hc.ι_injective_of_maps_injective hF a
  let A := (D ⊗ D).obj a
  let fstA : k.obj A ⟶ k.obj (D.obj a) := by
    change k.obj (D.obj a ⊗ D.obj a) ⟶ k.obj (D.obj a)
    exact k.map (CartesianMonoidalCategory.fst (D.obj a) (D.obj a))
  let sndA : k.obj A ⟶ k.obj (D.obj a) := by
    change k.obj (D.obj a ⊗ D.obj a) ⟶ k.obj (D.obj a)
    exact k.map (CartesianMonoidalCategory.snd (D.obj a) (D.obj a))
  let diagonalA : Set (k.obj A) := {p | fstA p = sndA p}
  have hdiagonalA : IsClosed diagonalA :=
    (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
      (D.obj a)).mp (F.obj a).is_weakHausdorff
  let leg : k.obj (D.obj a) ⟶ k.obj L := by
    change k.obj (D.obj a) ⟶ k.obj c.pt
    exact k.map (c.ι.app a)
  have hcFst : cTop.ι.app a ≫ fstL = fstA ≫ leg := by
    change k.map (c₂.ι.app a) ≫
        k.map (CartesianMonoidalCategory.fst L L) =
      k.map (CartesianMonoidalCategory.fst (D.obj a) (D.obj a)) ≫
        k.map (c.ι.app a)
    dsimp [c₂]
    rw [← k.map_comp, ← k.map_comp]
    exact congrArg k.map (CartesianMonoidalCategory.tensorHom_fst _ _)
  have hcSnd : cTop.ι.app a ≫ sndL = sndA ≫ leg := by
    change k.map (c₂.ι.app a) ≫
        k.map (CartesianMonoidalCategory.snd L L) =
      k.map (CartesianMonoidalCategory.snd (D.obj a) (D.obj a)) ≫
        k.map (c.ι.app a)
    dsimp [c₂]
    rw [← k.map_comp, ← k.map_comp]
    exact congrArg k.map (CartesianMonoidalCategory.tensorHom_snd _ _)
  have hinjTop : Function.Injective leg := by
    dsimp [leg]
    exact hinj
  rw [show cTop.ι.app a ⁻¹' diagonal = diagonalA by
    ext p
    change (cTop.ι.app a p ∈ diagonal) ↔ (p ∈ diagonalA)
    dsimp [diagonal, diagonalA]
    have hcFstP := ConcreteCategory.congr_hom hcFst p
    have hcSndP := ConcreteCategory.congr_hom hcSnd p
    simp only [ConcreteCategory.comp_apply] at hcFstP hcSndP
    constructor
    · intro hp
      apply hinjTop
      exact hcFstP.symm.trans (hp.trans hcSndP)
    · intro hp
      exact hcFstP.trans
        ((congrArg (fun z => leg z) hp).trans hcSndP.symm)]
  exact hdiagonalA

private noncomputable def
    colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff
    {I : Type v} [Category.{v} I] (F : I ⥤ CGWH.{u, v})
    (hL : UWeakHausdorffSpace.{u}
      ((Limits.colimit (F ⋙ cgwhToCompactlyGenerated) :
        CompactlyGenerated.{u, v}) : Type v)) :
    Limits.colimit (F ⋙ cgwhToCompactlyGenerated) ≅
      cgwhToCompactlyGenerated.obj (Limits.colimit F) := by
  let j := cgwhToCompactlyGenerated.{u, v}
  let k := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  let D := F ⋙ j
  let sourceIso : k.obj (Limits.colimit D) ≅
      Limits.colimit (F ⋙ cgwhToTop) :=
    preservesColimitIso k D ≪≫
      HasColimit.isoOfNatIso (Functor.associator F j k)
  have hRaw : UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (F ⋙ cgwhToTop)) := by
    let e := TopCat.homeoOfIso sourceIso
    refine ⟨fun K f => ?_⟩
    let f' : C(K, k.obj (Limits.colimit D)) :=
      ⟨fun x => e.symm (f x), e.symm.continuous.comp f.continuous⟩
    have hclosed : IsClosed (Set.range f') := hL.isClosed_range K f'
    have hrange : Set.range f = e '' Set.range f' := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨f' x, ⟨x, rfl⟩, e.apply_symm_apply (f x)⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, (e.apply_symm_apply (f x)).symm⟩
    rw [hrange]
    exact e.isClosedMap _ hclosed
  have hComparison : IsHomeomorph (colimitComparisonFromTop F) :=
    (colimitComparisonFromTop_isHomeomorph_iff F).2 hRaw
  let _ : IsIso (colimitComparisonFromTop F) :=
    (TopCat.isIso_iff_isHomeomorph _).2 hComparison
  exact CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop.preimageIso
    (sourceIso ≪≫ asIso (colimitComparisonFromTop F))

@[reassoc]
private theorem
    colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff_hom_ι
    {I : Type v} [Category.{v} I] (F : I ⥤ CGWH.{u, v})
    (hL : UWeakHausdorffSpace.{u}
      ((Limits.colimit (F ⋙ cgwhToCompactlyGenerated) :
        CompactlyGenerated.{u, v}) : Type v)) (a : I) :
    Limits.colimit.ι (F ⋙ cgwhToCompactlyGenerated) a ≫
        (colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff
          F hL).hom =
      cgwhToCompactlyGenerated.map (Limits.colimit.ι F a) := by
  let j := cgwhToCompactlyGenerated.{u, v}
  let k := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  let D := F ⋙ j
  let sourceIso : k.obj (Limits.colimit D) ≅
      Limits.colimit (F ⋙ cgwhToTop) :=
    preservesColimitIso k D ≪≫
      HasColimit.isoOfNatIso (Functor.associator F j k)
  have hRaw : UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (F ⋙ cgwhToTop)) := by
    let e := TopCat.homeoOfIso sourceIso
    refine ⟨fun K f => ?_⟩
    let f' : C(K, k.obj (Limits.colimit D)) :=
      ⟨fun x => e.symm (f x), e.symm.continuous.comp f.continuous⟩
    have hclosed : IsClosed (Set.range f') := hL.isClosed_range K f'
    have hrange : Set.range f = e '' Set.range f' := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨f' x, ⟨x, rfl⟩, e.apply_symm_apply (f x)⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, (e.apply_symm_apply (f x)).symm⟩
    rw [hrange]
    exact e.isClosedMap _ hclosed
  let _ : IsIso (colimitComparisonFromTop F) :=
    (TopCat.isIso_iff_isHomeomorph _).2
      ((colimitComparisonFromTop_isHomeomorph_iff F).2 hRaw)
  apply k.map_injective
  change k.map (Limits.colimit.ι (F ⋙ j) a) ≫
      k.map
        (CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop.preimage
          ((preservesColimitIso k (F ⋙ j) ≪≫
            HasColimit.isoOfNatIso (Functor.associator F j k) ≪≫
              asIso (colimitComparisonFromTop F)).hom)) =
    k.map (j.map (Limits.colimit.ι F a))
  dsimp [k]
  rw [CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop.map_preimage]
  rw [ι_preservesColimitIso_hom_assoc]
  rw [HasColimit.ι_isoOfNatIso_hom_assoc]
  exact colimitComparisonFromTop_ι F a

private noncomputable def
    isColimit_mapCocone_cgwhToCompactlyGenerated_of_weakHausdorff
    {I : Type v} [Category.{v} I] (F : I ⥤ CGWH.{u, v})
    (c : Cocone F) (hc : IsColimit c)
    (hL : UWeakHausdorffSpace.{u}
      ((Limits.colimit (F ⋙ cgwhToCompactlyGenerated) :
        CompactlyGenerated.{u, v}) : Type v)) :
    IsColimit (cgwhToCompactlyGenerated.mapCocone c) := by
  let j := cgwhToCompactlyGenerated.{u, v}
  let e₀ := colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff F hL
  let e₁ := j.mapIso
    ((Limits.colimit.isColimit F).coconePointUniqueUpToIso hc)
  exact IsColimit.ofIsoColimit (Limits.colimit.isColimit (F ⋙ j))
    (Cocone.ext (e₀ ≪≫ e₁) (by
      intro a
      dsimp [e₀, e₁, j]
      rw [colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff_hom_ι_assoc]
      rw [← j.map_comp]
      apply congrArg j.map
      exact IsColimit.comp_coconePointUniqueUpToIso_hom
        (Limits.colimit.isColimit F) hc a))

/-- A filtered diagram with injective original maps has a weak-Hausdorff
compactly generated colimit, with the original object and Hom universes. -/
theorem compactlyGeneratedColimit_isWeakHausdorff_of_maps_injective
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (F : I ⥤ CGWH.{u, v})
    (hF : ∀ ⦃a b : I⦄ (f : a ⟶ b), Function.Injective
      (cgwhToCompactlyGenerated.map (F.map f)).hom) :
    UWeakHausdorffSpace.{u}
      ((Limits.colimit (F ⋙ cgwhToCompactlyGenerated) :
        CompactlyGenerated.{u, v}) : Type v) :=
  compactlyGeneratedColimit_isWeakHausdorff_of_injective F hF

/-- The caller's original CGWH colimit cocone remains colimiting after the
actual inclusion whenever its compactly generated colimit is weak Hausdorff. -/
@[no_expose]
noncomputable def isColimitMapCoconeOfWeakHausdorff
    {I : Type v} [Category.{v} I] (F : I ⥤ CGWH.{u, v})
    (c : Cocone F) (hc : IsColimit c)
    (hL : UWeakHausdorffSpace.{u}
      ((Limits.colimit (F ⋙ cgwhToCompactlyGenerated) :
        CompactlyGenerated.{u, v}) : Type v)) :
    IsColimit (cgwhToCompactlyGenerated.mapCocone c) :=
  isColimit_mapCocone_cgwhToCompactlyGenerated_of_weakHausdorff F c hc hL

section Transfinite

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

theorem injective_map_of_injective_succ
    (F : J ⥤ CGWH.{u, v}) [F.IsWellOrderContinuous]
    (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (cgwhToCompactlyGenerated.map
        (F.map (homOfLE (Order.le_succ a)))).hom)
    {a b : J} (f : a ⟶ b) : Function.Injective
      (cgwhToCompactlyGenerated.map (F.map f)).hom := by
  let j := cgwhToCompactlyGenerated.{u, v}
  have aux (b : J) : ∀ (a : J) (h : a ≤ b), Function.Injective
      (j.map (F.map (homOfLE h))).hom := by
    induction b using SuccOrder.limitRecOn with
    | isMin b hb =>
        intro a h
        have hab : a = b := hb.eq_of_le h
        subst a
        have hh : (homOfLE h : b ⟶ b) = 𝟙 b := Subsingleton.elim _ _
        rw [hh, F.map_id, j.map_id]
        intro x y hxy
        change x = y at hxy
        exact hxy
    | succ b hb ih =>
        intro a h
        obtain rfl | hab := Order.le_succ_iff_eq_or_le.mp h
        · have hh : (homOfLE h : Order.succ b ⟶ Order.succ b) =
              𝟙 (Order.succ b) := Subsingleton.elim _ _
          rw [hh, F.map_id, j.map_id]
          intro x y hxy
          change x = y at hxy
          exact hxy
        · rw [← homOfLE_comp hab (Order.le_succ b), F.map_comp, j.map_comp]
          exact (hSucc b hb).comp (ih a hab)
    | isSuccLimit b hb ih =>
        intro a h
        by_cases hab : a = b
        · subst a
          have hh : (homOfLE h : b ⟶ b) = 𝟙 b := Subsingleton.elim _ _
          rw [hh, F.map_id, j.map_id]
          intro x y hxy
          change x = y at hxy
          exact hxy
        · have ha : a < b := lt_of_le_of_ne h hab
          let _ : Nonempty (Set.Iio b) := ⟨⟨⊥, hb.bot_lt⟩⟩
          let _ : IsFiltered (Set.Iio b) := by infer_instance
          let R := (Set.principalSegIio b).monotone.functor ⋙ F
          have hR : ∀ ⦃x y : Set.Iio b⦄ (g : x ⟶ y), Function.Injective
              (j.map (R.map g)).hom := by
            intro x y g
            change Function.Injective
              (j.map (F.map ((Set.principalSegIio b).monotone.functor.map g))).hom
            have hg : (Set.principalSegIio b).monotone.functor.map g =
                homOfLE (leOfHom g) := Subsingleton.elim _ _
            rw [hg]
            exact ih y.1 y.2 x.1 (leOfHom g)
          have hWeak : UWeakHausdorffSpace.{u}
              ((Limits.colimit (R ⋙ j) : CompactlyGenerated.{u, v}) : Type v) :=
            compactlyGeneratedColimit_isWeakHausdorff_of_injective R hR
          let cLimit := (Set.principalSegIio b).cocone F
          let hcLimit := F.isColimitOfIsWellOrderContinuous b hb
          have hcMapped : IsColimit (j.mapCocone cLimit) :=
            isColimit_mapCocone_cgwhToCompactlyGenerated_of_weakHausdorff
              R cLimit hcLimit hWeak
          let _ : PreservesColimitsOfShape (Set.Iio b)
              (forget CompactlyGenerated) := by
            change PreservesColimitsOfShape (Set.Iio b)
              (CompactlyGenerated.compactlyGeneratedToTop ⋙ forget TopCat)
            infer_instance
          have hleg := hcMapped.ι_injective_of_maps_injective hR ⟨a, ha⟩
          change Function.Injective
            (j.map (F.map (homOfLE ha.le))).hom at hleg
          have hp : (homOfLE ha.le : a ⟶ b) = homOfLE h :=
            Subsingleton.elim _ _
          rw [hp] at hleg
          exact hleg
  have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  simpa only [hf] using aux b a (leOfHom f)

theorem compactlyGeneratedColimit_isWeakHausdorff_of_injective_succ
    (F : J ⥤ CGWH.{u, v}) [F.IsWellOrderContinuous]
    (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (cgwhToCompactlyGenerated.map
        (F.map (homOfLE (Order.le_succ a)))).hom) :
    UWeakHausdorffSpace.{u}
      ((Limits.colimit (F ⋙ cgwhToCompactlyGenerated) :
        CompactlyGenerated.{u, v}) : Type v) :=
  compactlyGeneratedColimit_isWeakHausdorff_of_injective F
    (fun _ _ f => injective_map_of_injective_succ F hSucc f)

/-- The compactly generated colimit of the chain is the underlying CGWH colimit. -/
@[no_expose]
noncomputable def transfiniteColimitComparisonIso
    (F : J ⥤ CGWH.{u, v}) [F.IsWellOrderContinuous]
    (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (cgwhToCompactlyGenerated.map
        (F.map (homOfLE (Order.le_succ a)))).hom) :
    Limits.colimit (F ⋙ cgwhToCompactlyGenerated) ≅
      cgwhToCompactlyGenerated.obj (Limits.colimit F) :=
  colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff F
    (compactlyGeneratedColimit_isWeakHausdorff_of_injective_succ F hSucc)

@[reassoc]
theorem transfiniteColimitComparisonIso_hom_ι
    (F : J ⥤ CGWH.{u, v}) [F.IsWellOrderContinuous]
    (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (cgwhToCompactlyGenerated.map
        (F.map (homOfLE (Order.le_succ a)))).hom)
    (a : J) :
    Limits.colimit.ι (F ⋙ cgwhToCompactlyGenerated) a ≫
        (transfiniteColimitComparisonIso F hSucc).hom =
      cgwhToCompactlyGenerated.map (Limits.colimit.ι F a) :=
  by
    unfold transfiniteColimitComparisonIso
    exact colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff_hom_ι
      F (compactlyGeneratedColimit_isWeakHausdorff_of_injective_succ F hSucc) a

/-- The inclusion into compactly generated spaces sends any colimit cocone
of an injective-successor continuous chain to a colimit cocone. -/
@[no_expose]
noncomputable def isColimitMapCoconeOfInjectiveSucc
    (F : J ⥤ CGWH.{u, v}) [F.IsWellOrderContinuous]
    (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (cgwhToCompactlyGenerated.map
        (F.map (homOfLE (Order.le_succ a)))).hom)
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit (cgwhToCompactlyGenerated.mapCocone c) := by
  let j := cgwhToCompactlyGenerated.{u, v}
  let eNative : Limits.colimit F ≅ c.pt :=
    (Limits.colimit.isColimit F).coconePointUniqueUpToIso hc
  let e : Limits.colimit (F ⋙ j) ≅ j.obj c.pt :=
    transfiniteColimitComparisonIso F hSucc ≪≫ j.mapIso eNative
  apply IsColimit.ofIsoColimit (Limits.colimit.isColimit (F ⋙ j))
  refine Cocone.ext e (fun a => ?_)
  change Limits.colimit.ι (F ⋙ j) a ≫ e.hom = j.map (c.ι.app a)
  dsimp [e]
  rw [transfiniteColimitComparisonIso_hom_ι_assoc]
  rw [← j.map_comp]
  exact j.congr_map
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (Limits.colimit.isColimit F) hc a)

theorem transfiniteColimit_ι_injective
    (F : J ⥤ CGWH.{u, v}) [F.IsWellOrderContinuous]
    (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (cgwhToCompactlyGenerated.map
        (F.map (homOfLE (Order.le_succ a)))).hom)
    (a : J) : Function.Injective
      (cgwhToCompactlyGenerated.map (Limits.colimit.ι F a)).hom := by
  let j := cgwhToCompactlyGenerated.{u, v}
  let _ : PreservesColimitsOfShape J (forget CompactlyGenerated) := by
    change PreservesColimitsOfShape J
      (CompactlyGenerated.compactlyGeneratedToTop ⋙ forget TopCat)
    infer_instance
  have hAmbient : Function.Injective
      (Limits.colimit.ι (F ⋙ j) a).hom :=
    (Limits.colimit.isColimit (F ⋙ j)).ι_injective_of_maps_injective
      (fun _ _ f => injective_map_of_injective_succ F hSucc f) a
  have hIso : Function.Injective
      (transfiniteColimitComparisonIso F hSucc).hom :=
    (CompactlyGenerated.homeoOfIso
      (transfiniteColimitComparisonIso F hSucc)).injective
  intro x y hxy
  apply hAmbient
  apply hIso
  have hx := ConcreteCategory.congr_hom
    (transfiniteColimitComparisonIso_hom_ι F hSucc a) x
  have hy := ConcreteCategory.congr_hom
    (transfiniteColimitComparisonIso_hom_ι F hSucc a) y
  simp only [ConcreteCategory.comp_apply] at hx hy
  exact hx.trans (hxy.trans hy.symm)

end Transfinite

end CGWH

namespace CategoryTheory.TransfiniteCompositionOfShape

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

/-- Map the complete transfinite composition when every successor map is injective. -/
@[no_expose]
noncomputable def mapCgwhToCompactlyGeneratedOfInjective
    {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (c : CategoryTheory.TransfiniteCompositionOfShape J f)
    (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (CGWH.cgwhToCompactlyGenerated.map
        (c.F.map (homOfLE (Order.le_succ a)))).hom) :
    CategoryTheory.TransfiniteCompositionOfShape J
      (CGWH.cgwhToCompactlyGenerated.map f) where
  F := c.F ⋙ CGWH.cgwhToCompactlyGenerated
  isoBot := CGWH.cgwhToCompactlyGenerated.mapIso c.isoBot
  isWellOrderContinuous := by
    constructor
    intro m hm
    let _ : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
    let _ : IsFiltered (Set.Iio m) := by infer_instance
    let R := (Set.principalSegIio m).monotone.functor ⋙ c.F
    have hR : ∀ ⦃a b : Set.Iio m⦄ (g : a ⟶ b), Function.Injective
        (CGWH.cgwhToCompactlyGenerated.map (R.map g)).hom := by
      intro a b g
      change Function.Injective
        (CGWH.cgwhToCompactlyGenerated.map
          (c.F.map ((Set.principalSegIio m).monotone.functor.map g))).hom
      have hg : (Set.principalSegIio m).monotone.functor.map g =
          homOfLE (leOfHom g) := Subsingleton.elim _ _
      rw [hg]
      exact CGWH.injective_map_of_injective_succ c.F hSucc _
    have hWeak : UWeakHausdorffSpace.{u}
        ((Limits.colimit (R ⋙ CGWH.cgwhToCompactlyGenerated) :
          CompactlyGenerated.{u, v}) : Type v) :=
      CGWH.compactlyGeneratedColimit_isWeakHausdorff_of_injective R hR
    refine ⟨?_⟩
    have hMapped :=
      CGWH.isColimit_mapCocone_cgwhToCompactlyGenerated_of_weakHausdorff
        R ((Set.principalSegIio m).cocone c.F)
          (c.F.isColimitOfIsWellOrderContinuous m hm) hWeak
    exact IsColimit.ofIsoColimit hMapped (Cocone.ext (Iso.refl _))
  incl := Functor.whiskerRight c.incl CGWH.cgwhToCompactlyGenerated ≫
    (Functor.constComp _ _ _).hom
  isColimit := by
    exact CGWH.isColimit_mapCocone_cgwhToCompactlyGenerated_of_weakHausdorff
      c.F (Cocone.mk _ c.incl) c.isColimit
        (CGWH.compactlyGeneratedColimit_isWeakHausdorff_of_injective_succ
          c.F hSucc)
  fac := by simp [← Functor.map_comp]

/-- The mapped transfinite chain has the original diagram with the inclusion applied. -/
theorem mapCgwhToCompactlyGeneratedOfInjective_F
    {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (c : CategoryTheory.TransfiniteCompositionOfShape J f)
    (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (CGWH.cgwhToCompactlyGenerated.map
        (c.F.map (homOfLE (Order.le_succ a)))).hom) :
    (c.mapCgwhToCompactlyGeneratedOfInjective hSucc).F =
      c.F ⋙ CGWH.cgwhToCompactlyGenerated := by
  unfold mapCgwhToCompactlyGeneratedOfInjective
  rfl


/-- Deprecated alias retaining the original public colimit map. -/
@[deprecated mapCgwhToCompactlyGeneratedOfInjective (since := "2026-11-06"), nolint defsWithUnderscore]
alias map_cgwhToCompactlyGenerated_of_injective := mapCgwhToCompactlyGeneratedOfInjective

end CategoryTheory.TransfiniteCompositionOfShape
