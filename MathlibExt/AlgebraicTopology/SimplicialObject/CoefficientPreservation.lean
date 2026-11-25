/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module
public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeLatchingFunctor
public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatchingFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Coefficient functors and relative Reedy arrows

Postcomposition compares the actual chosen latching and matching objects and relative arrows.
The latching and matching constructions require preservation of their own index shape and of
pushouts or pullbacks, respectively. All coefficient categories have independent universes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D) (k : ℕ)

section LatchingObjects

variable [HasColimitsOfShape (latchingIndex k) C]
  [HasColimitsOfShape (latchingIndex k) D]
  [PreservesColimitsOfShape (latchingIndex k) F]

/-- The standard preservation comparison for the chosen latching objects. -/
def coefficientLatchingObjectIso :
    latchingObjectFunctor (C := C) k ⋙ F ≅
      (whiskeringRight SimplexCategoryᵒᵖ C D).obj F ⋙ latchingObjectFunctor k := by
  refine NatIso.ofComponents (fun X => preservesColimitIso F (latchingDiagram X k)) ?_
  intro X Y f
  exact (preservesColimitNatIso (J := latchingIndex k) F).hom.naturality
    ((latchingDiagramFunctor k).map f)

/-- Both injection equations use the same chosen latching comparison. -/
theorem coefficientLatchingObject_legs (X : SimplicialObject C) (a : latchingIndex k) :
    (F.map (latchingι X k a) ≫ (coefficientLatchingObjectIso F k).hom.app X =
      latchingι (X ⋙ F) k a) ∧
    (latchingι (X ⋙ F) k a ≫ (coefficientLatchingObjectIso F k).inv.app X =
      F.map (latchingι X k a)) := by
  constructor
  · exact ι_preservesColimitIso_hom F (latchingDiagram X k) a
  · exact ι_preservesColimitIso_inv F (latchingDiagram X k) a

/-- The latching-map equations retain the original structure map in both directions. -/
theorem coefficientLatchingMap_equations (X : SimplicialObject C) :
    ((coefficientLatchingObjectIso F k).hom.app X ≫ latchingMap (X ⋙ F) k =
      F.map (latchingMap X k)) ∧
    ((coefficientLatchingObjectIso F k).inv.app X ≫ F.map (latchingMap X k) =
      latchingMap (X ⋙ F) k) := by
  let b := (coefficientLatchingObjectIso F k).app X
  have hinv : b.inv ≫ F.map (latchingMap X k) = latchingMap (X ⋙ F) k := by
    apply colimit.hom_ext
    intro a
    change latchingι (X ⋙ F) k a ≫ (b.inv ≫ F.map (latchingMap X k)) =
      latchingι (X ⋙ F) k a ≫ latchingMap (X ⋙ F) k
    have hb : latchingι (X ⋙ F) k a ≫ b.inv = F.map (latchingι X k a) :=
      (coefficientLatchingObject_legs F k X a).2
    rw [← Category.assoc, hb,
      ← F.map_comp, latchingMap_ι, latchingMap_ι]
    rfl
  exact ⟨(Iso.eq_inv_comp b).mp hinv.symm, hinv⟩

end LatchingObjects

section MatchingObjects

variable [HasLimitsOfShape (matchingIndex k) C]
  [HasLimitsOfShape (matchingIndex k) D]
  [PreservesLimitsOfShape (matchingIndex k) F]

/-- The standard preservation comparison for the chosen matching objects. -/
def coefficientMatchingObjectIso :
    matchingObjectFunctor (C := C) k ⋙ F ≅
      (whiskeringRight SimplexCategoryᵒᵖ C D).obj F ⋙ matchingObjectFunctor k := by
  refine NatIso.ofComponents (fun X => preservesLimitIso F (matchingDiagram X k)) ?_
  intro X Y f
  exact (preservesLimitNatIso (J := matchingIndex k) F).hom.naturality
    ((matchingDiagramFunctor k).map f)

/-- Both projection equations use the same chosen matching comparison. -/
theorem coefficientMatchingObject_legs (X : SimplicialObject C) (a : matchingIndex k) :
    ((coefficientMatchingObjectIso F k).hom.app X ≫ matchingπ (X ⋙ F) k a =
      F.map (matchingπ X k a)) ∧
    ((coefficientMatchingObjectIso F k).inv.app X ≫ F.map (matchingπ X k a) =
      matchingπ (X ⋙ F) k a) := by
  constructor
  · exact preservesLimitIso_hom_π F (matchingDiagram X k) a
  · exact preservesLimitIso_inv_π F (matchingDiagram X k) a

/-- The matching-map equations retain the original structure map in both directions. -/
theorem coefficientMatchingMap_equations (X : SimplicialObject C) :
    (F.map (matchingMap X k) ≫ (coefficientMatchingObjectIso F k).hom.app X =
      matchingMap (X ⋙ F) k) ∧
    (matchingMap (X ⋙ F) k ≫ (coefficientMatchingObjectIso F k).inv.app X =
      F.map (matchingMap X k)) := by
  let b := (coefficientMatchingObjectIso F k).app X
  have hhom : F.map (matchingMap X k) ≫ b.hom = matchingMap (X ⋙ F) k := by
    apply limit.hom_ext
    intro a
    change (F.map (matchingMap X k) ≫ b.hom) ≫ matchingπ (X ⋙ F) k a =
      matchingMap (X ⋙ F) k ≫ matchingπ (X ⋙ F) k a
    have hb : b.hom ≫ matchingπ (X ⋙ F) k a = F.map (matchingπ X k a) :=
      (coefficientMatchingObject_legs F k X a).1
    rw [Category.assoc, hb,
      ← F.map_comp, matchingMap_π, matchingMap_π]
    rfl
  exact ⟨hhom, (Iso.comp_inv_eq b).mpr hhom.symm⟩

end MatchingObjects


section RelativeLatching

variable [HasColimitsOfShape (latchingIndex k) C]
  [HasColimitsOfShape (latchingIndex k) D]
  [PreservesColimitsOfShape (latchingIndex k) F]
  [HasPushouts C] [HasPushouts D] [PreservesColimitsOfShape WalkingSpan F]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def relativeLatchingInl'
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    (k : ℕ) [HasColimitsOfShape (latchingIndex k) C]
    (f : Arrow (SimplicialObject C)) :
    f.left.obj (op ⦋k⦌) ⟶ ((relativeLatchingMapArrowFunctor k).obj f).left :=
  pushout.inl (latchingMap f.left k) ((latchingObjectFunctor k).map f.hom)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def relativeLatchingInr'
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    (k : ℕ) [HasColimitsOfShape (latchingIndex k) C]
    (f : Arrow (SimplicialObject C)) :
    latchingObject f.right k ⟶ ((relativeLatchingMapArrowFunctor k).obj f).left :=
  pushout.inr (latchingMap f.left k) ((latchingObjectFunctor k).map f.hom)

def coefficientRelativeLatchingSpanIso
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    span (F.map (latchingMap X k))
        (F.map ((latchingObjectFunctor (C := C) k).map f)) ≅
      span (latchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj X) k)
        ((latchingObjectFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) := by
  exact spanIsoMk (coefficientLatchingObjectIso F k |>.app X) (Iso.refl _)
    (coefficientLatchingObjectIso F k |>.app Y)
    (by
      change F.map (latchingMap X k) ≫ 𝟙 _ =
        (coefficientLatchingObjectIso F k).hom.app X ≫
          latchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj X) k
      rw [Category.comp_id]
      exact (coefficientLatchingMap_equations F k X).1.symm)
    (coefficientLatchingObjectIso F k |>.hom.naturality f)

noncomputable def coefficientRelativeLatchingSourceIso
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    F.obj (relativeLatchingObject f k) ≅
      relativeLatchingObject
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f) k := by
  exact (PreservesPushout.iso F (latchingMap X k)
    ((latchingObjectFunctor (C := C) k).map f)).symm ≪≫
      HasColimit.isoOfNatIso (coefficientRelativeLatchingSpanIso F k f)

@[reassoc]
theorem coefficientRelativeLatchingSourceIso_hom_inl
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    F.map (pushout.inl (latchingMap X k)
        ((latchingObjectFunctor (C := C) k).map f)) ≫
      (coefficientRelativeLatchingSourceIso F k f).hom =
    pushout.inl
      (latchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj X) k)
      ((latchingObjectFunctor (C := D) k).map
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) := by
  change _ ≫ ((PreservesPushout.iso F (latchingMap X k)
      ((latchingObjectFunctor (C := C) k).map f)).inv ≫
        (HasColimit.isoOfNatIso (coefficientRelativeLatchingSpanIso F k f)).hom) = _
  rw [← Category.assoc, PreservesPushout.inl_iso_inv, HasColimit.ι_isoOfNatIso_hom]
  change 𝟙 _ ≫ pushout.inl _ _ = pushout.inl _ _
  rw [Category.id_comp]

@[reassoc]
theorem coefficientRelativeLatchingSourceIso_hom_inr
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    F.map (pushout.inr (latchingMap X k)
        ((latchingObjectFunctor (C := C) k).map f)) ≫
      (coefficientRelativeLatchingSourceIso F k f).hom =
    (coefficientLatchingObjectIso F k).hom.app Y ≫
      pushout.inr
        (latchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj X) k)
        ((latchingObjectFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) := by
  change _ ≫ ((PreservesPushout.iso F (latchingMap X k)
      ((latchingObjectFunctor (C := C) k).map f)).inv ≫
        (HasColimit.isoOfNatIso (coefficientRelativeLatchingSpanIso F k f)).hom) = _
  rw [← Category.assoc, PreservesPushout.inr_iso_inv, HasColimit.ι_isoOfNatIso_hom]
  rfl

private theorem coefficientRelativeLatchingSourceIso_inv_inl
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    pushout.inl
        (latchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj X) k)
        ((latchingObjectFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) ≫
      (coefficientRelativeLatchingSourceIso F k f).inv =
    F.map (pushout.inl (latchingMap X k)
      ((latchingObjectFunctor (C := C) k).map f)) := by
  change _ ≫ ((HasColimit.isoOfNatIso (coefficientRelativeLatchingSpanIso F k f)).inv ≫
      (PreservesPushout.iso F (latchingMap X k)
        ((latchingObjectFunctor (C := C) k).map f)).hom) = _
  rw [← Category.assoc, HasColimit.ι_isoOfNatIso_inv]
  change (𝟙 _ ≫ pushout.inl _ _) ≫
      (PreservesPushout.iso F (latchingMap X k)
        ((latchingObjectFunctor (C := C) k).map f)).hom = _
  rw [Category.id_comp, PreservesPushout.inl_iso_hom]

private theorem coefficientRelativeLatchingSourceIso_inv_inr
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    pushout.inr
        (latchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj X) k)
        ((latchingObjectFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) ≫
      (coefficientRelativeLatchingSourceIso F k f).inv =
    (coefficientLatchingObjectIso F k).inv.app Y ≫
      F.map (pushout.inr (latchingMap X k)
        ((latchingObjectFunctor (C := C) k).map f)) := by
  change _ ≫ ((HasColimit.isoOfNatIso (coefficientRelativeLatchingSpanIso F k f)).inv ≫
      (PreservesPushout.iso F (latchingMap X k)
        ((latchingObjectFunctor (C := C) k).map f)).hom) = _
  rw [← Category.assoc, HasColimit.ι_isoOfNatIso_inv]
  rw [Category.assoc, PreservesPushout.inr_iso_hom]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
noncomputable def coefficientRelativeLatchingSourceFunctorIso
    (f : Arrow (SimplicialObject C)) :
    F.obj ((relativeLatchingMapArrowFunctor (C := C) k).obj f).left ≅
      ((relativeLatchingMapArrowFunctor (C := D) k).obj
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f)).left :=
  coefficientRelativeLatchingSourceIso F k f.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def coefficientRelativeLatchingInlD
    (f : Arrow (SimplicialObject C)) :
    (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f).left.obj
        (op ⦋k⦌) ⟶
      ((relativeLatchingMapArrowFunctor (C := D) k).obj
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f)).left :=
  relativeLatchingInl' k
    (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def coefficientRelativeLatchingInrD
    (f : Arrow (SimplicialObject C)) :
    latchingObject
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f).right k ⟶
      ((relativeLatchingMapArrowFunctor (C := D) k).obj
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f)).left :=
  relativeLatchingInr' k
    (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem coefficientRelativeLatchingSourceFunctorIso_hom_inl
    (f : Arrow (SimplicialObject C)) :
    F.map (relativeLatchingInl' k f) ≫
      (coefficientRelativeLatchingSourceFunctorIso F k f).hom =
    coefficientRelativeLatchingInlD F k f := by
  change F.map (pushout.inl (latchingMap f.left k)
      ((latchingObjectFunctor (C := C) k).map f.hom)) ≫
      (coefficientRelativeLatchingSourceIso F k f.hom).hom = _
  exact coefficientRelativeLatchingSourceIso_hom_inl F k f.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem coefficientRelativeLatchingSourceFunctorIso_hom_inr
    (f : Arrow (SimplicialObject C)) :
    F.map (relativeLatchingInr' k f) ≫
      (coefficientRelativeLatchingSourceFunctorIso F k f).hom =
    (coefficientLatchingObjectIso F k).hom.app f.right ≫
      coefficientRelativeLatchingInrD F k f := by
  change F.map (pushout.inr (latchingMap f.left k)
      ((latchingObjectFunctor (C := C) k).map f.hom)) ≫
      (coefficientRelativeLatchingSourceIso F k f.hom).hom = _
  exact coefficientRelativeLatchingSourceIso_hom_inr F k f.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem coefficientRelativeLatchingSourceFunctorIso_inv_inl
    (f : Arrow (SimplicialObject C)) :
    coefficientRelativeLatchingInlD F k f ≫
      (coefficientRelativeLatchingSourceFunctorIso F k f).inv =
    F.map (relativeLatchingInl' k f) := by
  change pushout.inl _ _ ≫
      (coefficientRelativeLatchingSourceIso F k f.hom).inv = _
  exact coefficientRelativeLatchingSourceIso_inv_inl F k f.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem coefficientRelativeLatchingSourceFunctorIso_inv_inr
    (f : Arrow (SimplicialObject C)) :
    coefficientRelativeLatchingInrD F k f ≫
      (coefficientRelativeLatchingSourceFunctorIso F k f).inv =
    (coefficientLatchingObjectIso F k).inv.app f.right ≫
      F.map (relativeLatchingInr' k f) := by
  change pushout.inr _ _ ≫
      (coefficientRelativeLatchingSourceIso F k f.hom).inv =
    (coefficientLatchingObjectIso F k).inv.app f.right ≫
      F.map (pushout.inr (latchingMap f.left k)
        ((latchingObjectFunctor (C := C) k).map f.hom))
  exact coefficientRelativeLatchingSourceIso_inv_inr F k f.hom

set_option backward.isDefEq.respectTransparency false in
noncomputable def coefficientRelativeLatchingComponentIso
    (f : Arrow (SimplicialObject C)) :
    (F.mapArrow).obj ((relativeLatchingMapArrowFunctor k).obj f) ≅
      (relativeLatchingMapArrowFunctor k).obj
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f) := by
  refine Arrow.isoMk (coefficientRelativeLatchingSourceFunctorIso F k f) (Iso.refl _) ?_
  change (coefficientRelativeLatchingSourceIso F k f.hom).hom ≫
      relativeLatchingMap
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f.hom) k =
    F.map (relativeLatchingMap f.hom k) ≫ 𝟙 _
  rw [Category.comp_id]
  apply (cancel_epi (PreservesPushout.iso F (latchingMap f.left k)
    ((latchingObjectFunctor (C := C) k).map f.hom)).hom).mp
  apply pushout.hom_ext
  · rw [PreservesPushout.inl_iso_hom_assoc]
    rw [coefficientRelativeLatchingSourceIso_hom_inl_assoc]
    rw [PreservesPushout.inl_iso_hom_assoc]
    rw [relativeLatchingMap_inl]
    rw [← F.map_comp, relativeLatchingMap_inl]
    rfl
  · rw [PreservesPushout.inr_iso_hom_assoc]
    rw [coefficientRelativeLatchingSourceIso_hom_inr_assoc]
    rw [PreservesPushout.inr_iso_hom_assoc]
    rw [relativeLatchingMap_inr]
    rw [← F.map_comp, relativeLatchingMap_inr]
    exact (coefficientLatchingMap_equations F k f.right).1

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem coefficientRelativeLatchingSourceIso_naturality
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    F.map (((relativeLatchingMapArrowFunctor (C := C) k).map q).left) ≫
        (coefficientRelativeLatchingSourceFunctorIso F k g).hom =
      (coefficientRelativeLatchingSourceFunctorIso F k f).hom ≫
        ((relativeLatchingMapArrowFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)).left := by
  have hCInl :
      F.map (relativeLatchingInl' k f) ≫
        F.map (((relativeLatchingMapArrowFunctor (C := C) k).map q).left) =
      F.map (q.left.app (op ⦋k⦌)) ≫
        F.map (relativeLatchingInl' k g) := by
    simpa only [relativeLatchingInl', Functor.map_comp] using
      congrArg (fun t => F.map t)
        (relativeLatchingMapArrowFunctor_map_left_inl k q)
  have hCInr :
      F.map (relativeLatchingInr' k f) ≫
        F.map (((relativeLatchingMapArrowFunctor (C := C) k).map q).left) =
      F.map ((latchingObjectFunctor (C := C) k).map q.right) ≫
        F.map (relativeLatchingInr' k g) := by
    simpa only [relativeLatchingInr', Functor.map_comp] using
      congrArg (fun t => F.map t)
        (relativeLatchingMapArrowFunctor_map_left_inr k q)
  have hDInl :
      coefficientRelativeLatchingInlD F k f ≫
          ((relativeLatchingMapArrowFunctor (C := D) k).map
            (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)).left =
        ((((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q).left.app
          (op ⦋k⦌)) ≫ coefficientRelativeLatchingInlD F k g := by
    simpa only [coefficientRelativeLatchingInlD, relativeLatchingInl'] using
      (relativeLatchingMapArrowFunctor_map_left_inl k
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q))
  have hDInr :
      coefficientRelativeLatchingInrD F k f ≫
          ((relativeLatchingMapArrowFunctor (C := D) k).map
            (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)).left =
        (latchingObjectFunctor (C := D) k).map
            (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q).right ≫
          coefficientRelativeLatchingInrD F k g := by
    simpa only [coefficientRelativeLatchingInrD, relativeLatchingInr'] using
      (relativeLatchingMapArrowFunctor_map_left_inr k
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q))
  apply (cancel_epi (PreservesPushout.iso F (latchingMap f.left k)
    ((latchingObjectFunctor (C := C) k).map f.hom)).hom).mp
  apply pushout.hom_ext
  · rw [PreservesPushout.inl_iso_hom_assoc]
    rw [PreservesPushout.inl_iso_hom_assoc]
    change F.map (relativeLatchingInl' k f) ≫ _ =
      F.map (relativeLatchingInl' k f) ≫ _
    rw [coefficientRelativeLatchingSourceFunctorIso_hom_inl_assoc]
    rw [hDInl]
    rw [← Category.assoc, hCInl, Category.assoc]
    rw [coefficientRelativeLatchingSourceFunctorIso_hom_inl]
    exact congrArg (fun h => h ≫ pushout.inl _ _)
      ((by rfl))
  · rw [PreservesPushout.inr_iso_hom_assoc]
    rw [PreservesPushout.inr_iso_hom_assoc]
    change F.map (relativeLatchingInr' k f) ≫ _ =
      F.map (relativeLatchingInr' k f) ≫ _
    rw [coefficientRelativeLatchingSourceFunctorIso_hom_inr_assoc]
    rw [hDInr]
    rw [← Category.assoc, hCInr, Category.assoc]
    rw [coefficientRelativeLatchingSourceFunctorIso_hom_inr]
    simpa [Functor.comp_map, Category.assoc, Functor.mapArrow] using
      congrArg (fun t => t ≫ coefficientRelativeLatchingInrD F k g)
        ((coefficientLatchingObjectIso F k).hom.naturality q.right)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition compares the whole relative latching Arrow functor. -/
noncomputable def coefficientRelativeLatchingArrowIso :
  relativeLatchingMapArrowFunctor (C := C) k ⋙ F.mapArrow ≅
    ((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow ⋙
        relativeLatchingMapArrowFunctor (C := D) k := by
  refine NatIso.ofComponents (fun f => coefficientRelativeLatchingComponentIso F k f) ?_
  intro f g q
  apply Arrow.hom_ext
  · exact coefficientRelativeLatchingSourceIso_naturality F k q
  · change F.map (q.right.app (op ⦋k⦌)) ≫ 𝟙 _ =
      𝟙 _ ≫ (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map q.right).app (op ⦋k⦌)
    simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Both directions preserve each chosen pushout injection and the target identity. -/
theorem coefficientRelativeLatching_equations {X Y : SimplicialObject C} (f : X ⟶ Y) :
  let a := (coefficientRelativeLatchingArrowIso F k).app (Arrow.mk f)
  (F.map (pushout.inl (latchingMap X k) ((latchingObjectFunctor (C := C) k).map f)) ≫
      a.hom.left = pushout.inl (latchingMap (X ⋙ F) k)
        ((latchingObjectFunctor (C := D) k).map (whiskerRight f F))) ∧
  (F.map (pushout.inr (latchingMap X k) ((latchingObjectFunctor (C := C) k).map f)) ≫ a.hom.left =
    (coefficientLatchingObjectIso F k).hom.app Y ≫ pushout.inr (latchingMap (X ⋙ F) k)
      ((latchingObjectFunctor (C := D) k).map (whiskerRight f F))) ∧
  (pushout.inl (latchingMap (X ⋙ F) k)
      ((latchingObjectFunctor (C := D) k).map (whiskerRight f F)) ≫ a.inv.left =
    F.map (pushout.inl (latchingMap X k) ((latchingObjectFunctor (C := C) k).map f))) ∧
  (pushout.inr (latchingMap (X ⋙ F) k)
      ((latchingObjectFunctor (C := D) k).map (whiskerRight f F)) ≫ a.inv.left =
    (coefficientLatchingObjectIso F k).inv.app Y ≫
      F.map (pushout.inr (latchingMap X k) ((latchingObjectFunctor (C := C) k).map f))) ∧
  (a.hom.right = 𝟙 (F.obj (Y.obj (op ⦋k⦌)))) ∧
  (a.inv.right = 𝟙 (F.obj (Y.obj (op ⦋k⦌)))) := by
  dsimp only [coefficientRelativeLatchingArrowIso]
  exact ⟨coefficientRelativeLatchingSourceFunctorIso_hom_inl F k (Arrow.mk f),
    coefficientRelativeLatchingSourceFunctorIso_hom_inr F k (Arrow.mk f),
    coefficientRelativeLatchingSourceFunctorIso_inv_inl F k (Arrow.mk f),
    coefficientRelativeLatchingSourceFunctorIso_inv_inr F k (Arrow.mk f), rfl, rfl⟩

end RelativeLatching

section RelativeMatching

variable [HasLimitsOfShape (matchingIndex k) C]
  [HasLimitsOfShape (matchingIndex k) D]
  [PreservesLimitsOfShape (matchingIndex k) F]
  [HasPullbacks C] [HasPullbacks D] [PreservesLimitsOfShape WalkingCospan F]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def relativeMatchingFst'
    {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
    (k : ℕ) [HasLimitsOfShape (matchingIndex k) C]
    (f : Arrow (SimplicialObject C)) :
    ((relativeMatchingMapArrowFunctor k).obj f).right ⟶ f.right.obj (op ⦋k⦌) :=
  pullback.fst (matchingMap f.right k) ((matchingObjectFunctor k).map f.hom)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def relativeMatchingSnd'
    {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
    (k : ℕ) [HasLimitsOfShape (matchingIndex k) C]
    (f : Arrow (SimplicialObject C)) :
    ((relativeMatchingMapArrowFunctor k).obj f).right ⟶ matchingObject f.left k :=
  pullback.snd (matchingMap f.right k) ((matchingObjectFunctor k).map f.hom)

def coefficientRelativeMatchingCospanIso
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    cospan (F.map (matchingMap Y k))
        (F.map ((matchingObjectFunctor (C := C) k).map f)) ≅
      cospan (matchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj Y) k)
        ((matchingObjectFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) := by
  exact cospanIsoMk (coefficientMatchingObjectIso F k |>.app Y) (Iso.refl _)
    (coefficientMatchingObjectIso F k |>.app X)
    (by
      change F.map (matchingMap Y k) ≫
          (coefficientMatchingObjectIso F k).hom.app Y =
        𝟙 _ ≫ matchingMap
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj Y) k
      rw [Category.id_comp]
      exact (coefficientMatchingMap_equations F k Y).1)
    (coefficientMatchingObjectIso F k |>.hom.naturality f)

noncomputable def coefficientRelativeMatchingTargetIso
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    F.obj (relativeMatchingObject f k) ≅
      relativeMatchingObject
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f) k := by
  exact PreservesPullback.iso F (matchingMap Y k)
      ((matchingObjectFunctor (C := C) k).map f) ≪≫
    HasLimit.isoOfNatIso (coefficientRelativeMatchingCospanIso F k f)

@[reassoc]
theorem coefficientRelativeMatchingTargetIso_hom_fst
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (coefficientRelativeMatchingTargetIso F k f).hom ≫
      pullback.fst
        (matchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj Y) k)
        ((matchingObjectFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) =
    F.map (pullback.fst (matchingMap Y k)
      ((matchingObjectFunctor (C := C) k).map f)) := by
  change ((PreservesPullback.iso F (matchingMap Y k)
      ((matchingObjectFunctor (C := C) k).map f)).hom ≫
        (HasLimit.isoOfNatIso (coefficientRelativeMatchingCospanIso F k f)).hom) ≫ _ = _
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π]
  change (PreservesPullback.iso F (matchingMap Y k)
      ((matchingObjectFunctor (C := C) k).map f)).hom ≫
        (pullback.fst (F.map (matchingMap Y k))
          (F.map ((matchingObjectFunctor (C := C) k).map f)) ≫ 𝟙 _) = _
  rw [Category.comp_id, PreservesPullback.iso_hom_fst]

@[reassoc]
theorem coefficientRelativeMatchingTargetIso_hom_snd
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (coefficientRelativeMatchingTargetIso F k f).hom ≫
      pullback.snd
        (matchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj Y) k)
        ((matchingObjectFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) =
    F.map (pullback.snd (matchingMap Y k)
      ((matchingObjectFunctor (C := C) k).map f)) ≫
        (coefficientMatchingObjectIso F k).hom.app X := by
  change ((PreservesPullback.iso F (matchingMap Y k)
      ((matchingObjectFunctor (C := C) k).map f)).hom ≫
        (HasLimit.isoOfNatIso (coefficientRelativeMatchingCospanIso F k f)).hom) ≫ _ = _
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc, PreservesPullback.iso_hom_snd]
  rfl

@[reassoc]
private theorem coefficientRelativeMatchingTargetIso_inv_fst
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (coefficientRelativeMatchingTargetIso F k f).inv ≫
      F.map (pullback.fst (matchingMap Y k)
        ((matchingObjectFunctor (C := C) k).map f)) =
    pullback.fst
      (matchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj Y) k)
      ((matchingObjectFunctor (C := D) k).map
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) := by
  change ((HasLimit.isoOfNatIso (coefficientRelativeMatchingCospanIso F k f)).inv ≫
      (PreservesPullback.iso F (matchingMap Y k)
        ((matchingObjectFunctor (C := C) k).map f)).inv) ≫ _ = _
  rw [Category.assoc, PreservesPullback.iso_inv_fst]
  rw [HasLimit.isoOfNatIso_inv_π]
  change pullback.fst _ _ ≫ 𝟙 _ = _
  rw [Category.comp_id]

@[reassoc]
private theorem coefficientRelativeMatchingTargetIso_inv_snd
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (coefficientRelativeMatchingTargetIso F k f).inv ≫
      F.map (pullback.snd (matchingMap Y k)
        ((matchingObjectFunctor (C := C) k).map f)) =
    pullback.snd
      (matchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj Y) k)
      ((matchingObjectFunctor (C := D) k).map
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f)) ≫
      (coefficientMatchingObjectIso F k).inv.app X := by
  change ((HasLimit.isoOfNatIso (coefficientRelativeMatchingCospanIso F k f)).inv ≫
      (PreservesPullback.iso F (matchingMap Y k)
        ((matchingObjectFunctor (C := C) k).map f)).inv) ≫ _ = _
  rw [Category.assoc, PreservesPullback.iso_inv_snd]
  rw [HasLimit.isoOfNatIso_inv_π]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
noncomputable def coefficientRelativeMatchingTargetFunctorIso
    (f : Arrow (SimplicialObject C)) :
    F.obj ((relativeMatchingMapArrowFunctor (C := C) k).obj f).right ≅
      ((relativeMatchingMapArrowFunctor (C := D) k).obj
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f)).right :=
  coefficientRelativeMatchingTargetIso F k f.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem coefficientRelativeMatchingTargetFunctorIso_hom_fst
    (f : Arrow (SimplicialObject C)) :
    (coefficientRelativeMatchingTargetFunctorIso F k f).hom ≫
      relativeMatchingFst' k
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f) =
    F.map (relativeMatchingFst' k f) := by
  change (coefficientRelativeMatchingTargetIso F k f.hom).hom ≫
    pullback.fst _ _ = _
  exact coefficientRelativeMatchingTargetIso_hom_fst F k f.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem coefficientRelativeMatchingTargetFunctorIso_hom_snd
    (f : Arrow (SimplicialObject C)) :
    (coefficientRelativeMatchingTargetFunctorIso F k f).hom ≫
      relativeMatchingSnd' k
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f) =
    F.map (relativeMatchingSnd' k f) ≫
      (coefficientMatchingObjectIso F k).hom.app f.left := by
  change (coefficientRelativeMatchingTargetIso F k f.hom).hom ≫
    pullback.snd _ _ = _
  exact coefficientRelativeMatchingTargetIso_hom_snd F k f.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem coefficientRelativeMatchingTargetFunctorIso_inv_fst
    (f : Arrow (SimplicialObject C)) :
    (coefficientRelativeMatchingTargetFunctorIso F k f).inv ≫
      F.map (relativeMatchingFst' k f) =
    relativeMatchingFst' k
      (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f) := by
  change (coefficientRelativeMatchingTargetIso F k f.hom).inv ≫
    F.map (pullback.fst _ _) = pullback.fst _ _
  exact coefficientRelativeMatchingTargetIso_inv_fst F k f.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem coefficientRelativeMatchingTargetFunctorIso_inv_snd
    (f : Arrow (SimplicialObject C)) :
    (coefficientRelativeMatchingTargetFunctorIso F k f).inv ≫
      F.map (relativeMatchingSnd' k f) =
    relativeMatchingSnd' k
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f) ≫
      (coefficientMatchingObjectIso F k).inv.app f.left := by
  change (coefficientRelativeMatchingTargetIso F k f.hom).inv ≫
    F.map (pullback.snd _ _) = pullback.snd _ _ ≫ _
  exact coefficientRelativeMatchingTargetIso_inv_snd F k f.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
noncomputable def coefficientRelativeMatchingComponentIso
    (f : Arrow (SimplicialObject C)) :
    (F.mapArrow).obj ((relativeMatchingMapArrowFunctor k).obj f) ≅
      (relativeMatchingMapArrowFunctor k).obj
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f) := by
  refine Arrow.isoMk (Iso.refl _) (coefficientRelativeMatchingTargetFunctorIso F k f) ?_
  change 𝟙 _ ≫ relativeMatchingMap
      (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f.hom) k =
    F.map (relativeMatchingMap f.hom k) ≫
      (coefficientRelativeMatchingTargetIso F k f.hom).hom
  rw [Category.id_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, coefficientRelativeMatchingTargetIso_hom_fst]
    calc
      relativeMatchingMap
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f.hom) k ≫
          pullback.fst
            (matchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj f.right) k)
            ((matchingObjectFunctor (C := D) k).map
              (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f.hom)) =
        (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f.hom).app (op ⦋k⦌) :=
          relativeMatchingMap_fst _ k
      _ = F.map (f.hom.app (op ⦋k⦌)) :=
        (by rfl)
      _ = F.map (relativeMatchingMap f.hom k) ≫
          F.map (pullback.fst (matchingMap f.right k)
            ((matchingObjectFunctor (C := C) k).map f.hom)) := by
        rw [← F.map_comp, relativeMatchingMap_fst]
  · rw [Category.assoc, coefficientRelativeMatchingTargetIso_hom_snd]
    calc
      relativeMatchingMap
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f.hom) k ≫
          pullback.snd
            (matchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj f.right) k)
            ((matchingObjectFunctor (C := D) k).map
              (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map f.hom)) =
        matchingMap (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).obj f.left) k :=
          relativeMatchingMap_snd _ k
      _ = F.map (matchingMap f.left k) ≫
          (coefficientMatchingObjectIso F k).hom.app f.left :=
        (coefficientMatchingMap_equations F k f.left).1.symm
      _ = F.map (relativeMatchingMap f.hom k) ≫
          F.map (pullback.snd (matchingMap f.right k)
            ((matchingObjectFunctor (C := C) k).map f.hom)) ≫
          (coefficientMatchingObjectIso F k).hom.app f.left := by
        rw [← Category.assoc, ← F.map_comp, relativeMatchingMap_snd]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem coefficientRelativeMatchingTargetIso_naturality
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    F.map (((relativeMatchingMapArrowFunctor (C := C) k).map q).right) ≫
        (coefficientRelativeMatchingTargetFunctorIso F k g).hom =
      (coefficientRelativeMatchingTargetFunctorIso F k f).hom ≫
        ((relativeMatchingMapArrowFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)).right := by
  have hCFst :
      F.map (((relativeMatchingMapArrowFunctor (C := C) k).map q).right) ≫
          F.map (relativeMatchingFst' k g) =
        F.map (relativeMatchingFst' k f) ≫
          F.map (q.right.app (op ⦋k⦌)) := by
    simpa only [relativeMatchingFst', Functor.map_comp] using
      congrArg (fun t => F.map t)
        (relativeMatchingMapArrowFunctor_map_right_fst k q)
  have hCSnd :
      F.map (((relativeMatchingMapArrowFunctor (C := C) k).map q).right) ≫
          F.map (relativeMatchingSnd' k g) =
        F.map (relativeMatchingSnd' k f) ≫
          F.map ((matchingObjectFunctor (C := C) k).map q.left) := by
    simpa only [relativeMatchingSnd', Functor.map_comp] using
      congrArg (fun t => F.map t)
        (relativeMatchingMapArrowFunctor_map_right_snd k q)
  have hDFst :
      ((relativeMatchingMapArrowFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)).right ≫
        relativeMatchingFst' k
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj g) =
      relativeMatchingFst' k
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f) ≫
        ((((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q).right.app
          (op ⦋k⦌)) :=
    relativeMatchingMapArrowFunctor_map_right_fst k
      (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)
  have hDSnd :
      ((relativeMatchingMapArrowFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)).right ≫
        relativeMatchingSnd' k
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj g) =
      relativeMatchingSnd' k
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj f) ≫
        (matchingObjectFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q).left :=
    relativeMatchingMapArrowFunctor_map_right_snd k
      (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)
  apply pullback.hom_ext
  · change (F.map
        (((relativeMatchingMapArrowFunctor (C := C) k).map q).right) ≫
          (coefficientRelativeMatchingTargetFunctorIso F k g).hom) ≫
            relativeMatchingFst' k
              (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj g) =
      ((coefficientRelativeMatchingTargetFunctorIso F k f).hom ≫
        ((relativeMatchingMapArrowFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)).right) ≫
            relativeMatchingFst' k
              (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj g)
    rw [Category.assoc, coefficientRelativeMatchingTargetFunctorIso_hom_fst]
    rw [hCFst]
    rw [Category.assoc, hDFst]
    rw [coefficientRelativeMatchingTargetFunctorIso_hom_fst_assoc]
    exact congrArg (fun h => F.map (relativeMatchingFst' k f) ≫ h)
      ((by rfl))
  · change (F.map
        (((relativeMatchingMapArrowFunctor (C := C) k).map q).right) ≫
          (coefficientRelativeMatchingTargetFunctorIso F k g).hom) ≫
            relativeMatchingSnd' k
              (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj g) =
      ((coefficientRelativeMatchingTargetFunctorIso F k f).hom ≫
        ((relativeMatchingMapArrowFunctor (C := D) k).map
          (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.map q)).right) ≫
            relativeMatchingSnd' k
              (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow.obj g)
    rw [Category.assoc, coefficientRelativeMatchingTargetFunctorIso_hom_snd]
    rw [← Category.assoc, hCSnd, Category.assoc]
    change F.map (relativeMatchingSnd' k f) ≫
        (((matchingObjectFunctor (C := C) k ⋙ F).map q.left) ≫
          (coefficientMatchingObjectIso F k).hom.app g.left) = _
    rw [(coefficientMatchingObjectIso F k).hom.naturality q.left]
    rw [Category.assoc, hDSnd]
    rw [coefficientRelativeMatchingTargetFunctorIso_hom_snd_assoc]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition compares the whole relative matching Arrow functor. -/
noncomputable def coefficientRelativeMatchingArrowIso :
  relativeMatchingMapArrowFunctor (C := C) k ⋙ F.mapArrow ≅
    ((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).mapArrow ⋙
        relativeMatchingMapArrowFunctor (C := D) k := by
  refine NatIso.ofComponents (fun f => coefficientRelativeMatchingComponentIso F k f) ?_
  intro f g q
  apply Arrow.hom_ext
  · change F.map (q.left.app (op ⦋k⦌)) ≫ 𝟙 _ =
      𝟙 _ ≫ (((whiskeringRight SimplexCategoryᵒᵖ C D).obj F).map q.left).app (op ⦋k⦌)
    simp
  · exact coefficientRelativeMatchingTargetIso_naturality F k q

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Both directions preserve each chosen pullback projection and the source identity. -/
theorem coefficientRelativeMatching_equations {X Y : SimplicialObject C} (f : X ⟶ Y) :
  let a := (coefficientRelativeMatchingArrowIso F k).app (Arrow.mk f)
  (a.hom.right ≫ pullback.fst (matchingMap (Y ⋙ F) k)
      ((matchingObjectFunctor (C := D) k).map (whiskerRight f F)) =
    F.map (pullback.fst (matchingMap Y k) ((matchingObjectFunctor (C := C) k).map f))) ∧
  (a.hom.right ≫ pullback.snd (matchingMap (Y ⋙ F) k)
      ((matchingObjectFunctor (C := D) k).map (whiskerRight f F)) =
    F.map (pullback.snd (matchingMap Y k) ((matchingObjectFunctor (C := C) k).map f)) ≫
      (coefficientMatchingObjectIso F k).hom.app X) ∧
  (a.inv.right ≫ F.map (pullback.fst (matchingMap Y k)
      ((matchingObjectFunctor (C := C) k).map f)) =
    pullback.fst (matchingMap (Y ⋙ F) k)
      ((matchingObjectFunctor (C := D) k).map (whiskerRight f F))) ∧
  (a.inv.right ≫ F.map (pullback.snd (matchingMap Y k) ((matchingObjectFunctor (C := C) k).map f)) =
    pullback.snd (matchingMap (Y ⋙ F) k)
      ((matchingObjectFunctor (C := D) k).map (whiskerRight f F)) ≫
        (coefficientMatchingObjectIso F k).inv.app X) ∧
  (a.hom.left = 𝟙 (F.obj (X.obj (op ⦋k⦌)))) ∧
  (a.inv.left = 𝟙 (F.obj (X.obj (op ⦋k⦌)))) := by
  dsimp only [coefficientRelativeMatchingArrowIso]
  exact ⟨coefficientRelativeMatchingTargetFunctorIso_hom_fst F k (Arrow.mk f),
    coefficientRelativeMatchingTargetFunctorIso_hom_snd F k (Arrow.mk f),
    coefficientRelativeMatchingTargetFunctorIso_inv_fst F k (Arrow.mk f),
    coefficientRelativeMatchingTargetFunctorIso_inv_snd F k (Arrow.mk f), rfl, rfl⟩

end RelativeMatching

section LatchingUnit

variable (e : C ≌ D) (k : ℕ)
variable [HasColimitsOfShape (latchingIndex k) C]
  [HasColimitsOfShape (latchingIndex k) D]

private theorem coefficientLatchingObject_unit (X : SimplicialObject C) :
    e.unitIso.hom.app (latchingObject X k) ≫
        e.inverse.map ((coefficientLatchingObjectIso e.functor k).hom.app X) ≫
        (coefficientLatchingObjectIso e.inverse k).hom.app (X ⋙ e.functor) =
      (latchingObjectFunctor k).map
          ((Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e).unitIso.hom.app X) := by
  apply colimit.hom_ext
  intro a
  change latchingι X k a ≫
      (e.unitIso.hom.app (latchingObject X k) ≫
        e.inverse.map ((coefficientLatchingObjectIso e.functor k).hom.app X) ≫
        (coefficientLatchingObjectIso e.inverse k).hom.app (X ⋙ e.functor)) =
    latchingι X k a ≫
      (latchingObjectFunctor k).map
          ((Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e).unitIso.hom.app X)
  rw [latchingObjectFunctor_map_ι]
  have hn : latchingι X k a ≫ e.unitIso.hom.app (latchingObject X k) =
      e.unitIso.hom.app (X.obj a.obj.left) ≫ e.inverse.map (e.functor.map (latchingι X k a)) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      e.unitIso.hom.naturality (latchingι X k a)
  calc
    _ = (latchingι X k a ≫ e.unitIso.hom.app (latchingObject X k)) ≫
        e.inverse.map ((coefficientLatchingObjectIso e.functor k).hom.app X) ≫
        (coefficientLatchingObjectIso e.inverse k).hom.app (X ⋙ e.functor) := by
      simp only [Category.assoc]
    _ = (e.unitIso.hom.app (X.obj a.obj.left) ≫
        e.inverse.map (e.functor.map (latchingι X k a))) ≫
        e.inverse.map ((coefficientLatchingObjectIso e.functor k).hom.app X) ≫
        (coefficientLatchingObjectIso e.inverse k).hom.app (X ⋙ e.functor) := by rw [hn]
    _ = e.unitIso.hom.app (X.obj a.obj.left) ≫
        e.inverse.map (e.functor.map (latchingι X k a) ≫
          (coefficientLatchingObjectIso e.functor k).hom.app X) ≫
        (coefficientLatchingObjectIso e.inverse k).hom.app (X ⋙ e.functor) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = e.unitIso.hom.app (X.obj a.obj.left) ≫ e.inverse.map (latchingι (X ⋙ e.functor) k a) ≫
        (coefficientLatchingObjectIso e.inverse k).hom.app (X ⋙ e.functor) := by
      rw [(coefficientLatchingObject_legs e.functor k X a).1]
    _ = e.unitIso.hom.app (X.obj a.obj.left) ≫ latchingι ((X ⋙ e.functor) ⋙ e.inverse) k a := by
      rw [(coefficientLatchingObject_legs e.inverse k (X ⋙ e.functor) a).1]
    _ = _ := by simp [Equivalence.congrRight]

variable [HasPushouts C] [HasPushouts D]

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRelativeLatching_unit_hom (f : Arrow (SimplicialObject C)) :
    let A := Functor.mapArrowEquivalence e
    let B := Functor.mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
    let α := coefficientRelativeLatchingArrowIso e.functor k
    let β := coefficientRelativeLatchingArrowIso e.inverse k
    A.unitIso.hom.app ((relativeLatchingMapArrowFunctor (C := C) k).obj f) ≫
        A.inverse.map (α.hom.app f) ≫ β.hom.app (B.functor.obj f) =
      (relativeLatchingMapArrowFunctor (C := C) k).map (B.unitIso.hom.app f) := by
  let A := Functor.mapArrowEquivalence e
  let B := Functor.mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
  let α := coefficientRelativeLatchingArrowIso e.functor k
  let β := coefficientRelativeLatchingArrowIso e.inverse k
  let fF := Arrow.mk (whiskerRight f.hom e.functor)
  let fGF := Arrow.mk (whiskerRight (whiskerRight f.hom e.functor) e.inverse)
  change A.unitIso.hom.app ((relativeLatchingMapArrowFunctor (C := C) k).obj f) ≫
      A.inverse.map (α.hom.app f) ≫ β.hom.app fF =
    (relativeLatchingMapArrowFunctor (C := C) k).map (B.unitIso.hom.app f)
  apply Arrow.hom_ext
  · change e.unitIso.hom.app ((relativeLatchingMapArrowFunctor (C := C) k).obj f).left ≫
        e.inverse.map ((α.hom.app f).left) ≫ (β.hom.app fF).left =
      ((relativeLatchingMapArrowFunctor (C := C) k).map (B.unitIso.hom.app f)).left
    apply pushout.hom_ext
    · let i := relativeLatchingInl' k f
      have hn : i ≫ e.unitIso.hom.app ((relativeLatchingMapArrowFunctor (C := C) k).obj f).left =
          e.unitIso.hom.app (f.left.obj (op ⦋k⦌)) ≫ e.inverse.map (e.functor.map i) := by
        simpa only [Functor.id_map, Functor.comp_map] using e.unitIso.hom.naturality i
      have hα : e.functor.map i ≫ (α.hom.app f).left = relativeLatchingInl' k fF :=
        (coefficientRelativeLatching_equations e.functor k f.hom).1
      have hβ : e.inverse.map (relativeLatchingInl' k fF) ≫ (β.hom.app fF).left =
          relativeLatchingInl' k fGF :=
        (coefficientRelativeLatching_equations e.inverse k fF.hom).1
      have hh : i ≫ ((relativeLatchingMapArrowFunctor (C := C) k).map (B.unitIso.hom.app f)).left =
          e.unitIso.hom.app (f.left.obj (op ⦋k⦌)) ≫ relativeLatchingInl' k fGF := by
        simp [i, relativeLatchingInl', fGF, B, Functor.mapArrowEquivalence, Equivalence.congrRight]
      change i ≫ _ = i ≫ _
      calc
        _ = (i ≫ e.unitIso.hom.app ((relativeLatchingMapArrowFunctor (C := C) k).obj f).left) ≫
            e.inverse.map ((α.hom.app f).left) ≫ (β.hom.app fF).left := by
              simp only [Category.assoc]
        _ = (e.unitIso.hom.app (f.left.obj (op ⦋k⦌)) ≫ e.inverse.map (e.functor.map i)) ≫
            e.inverse.map ((α.hom.app f).left) ≫ (β.hom.app fF).left := by rw [hn]
        _ = e.unitIso.hom.app (f.left.obj (op ⦋k⦌)) ≫
            e.inverse.map (e.functor.map i ≫ (α.hom.app f).left) ≫ (β.hom.app fF).left := by
          simp only [Functor.map_comp, Category.assoc]
        _ = e.unitIso.hom.app (f.left.obj (op ⦋k⦌)) ≫
            e.inverse.map (relativeLatchingInl' k fF) ≫ (β.hom.app fF).left := by rw [hα]
        _ = e.unitIso.hom.app (f.left.obj (op ⦋k⦌)) ≫ relativeLatchingInl' k fGF := by rw [hβ]
        _ = _ := hh.symm
    · let j := relativeLatchingInr' k f
      have hn : j ≫ e.unitIso.hom.app ((relativeLatchingMapArrowFunctor (C := C) k).obj f).left =
          e.unitIso.hom.app (latchingObject f.right k) ≫ e.inverse.map (e.functor.map j) := by
        simpa only [Functor.id_map, Functor.comp_map] using e.unitIso.hom.naturality j
      have hα : e.functor.map j ≫ (α.hom.app f).left =
          (coefficientLatchingObjectIso e.functor k).hom.app f.right ≫ relativeLatchingInr' k fF :=
        (coefficientRelativeLatching_equations e.functor k f.hom).2.1
      have hβ : e.inverse.map (relativeLatchingInr' k fF) ≫ (β.hom.app fF).left =
          (coefficientLatchingObjectIso e.inverse k).hom.app fF.right ≫
              relativeLatchingInr' k fGF :=
        (coefficientRelativeLatching_equations e.inverse k fF.hom).2.1
      have hh : j ≫ ((relativeLatchingMapArrowFunctor (C := C) k).map (B.unitIso.hom.app f)).left =
          (latchingObjectFunctor k).map
              ((Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e).unitIso.hom.app f.right) ≫
            relativeLatchingInr' k fGF := by
        simp [j, relativeLatchingInr', fGF, B, Functor.mapArrowEquivalence]
      change j ≫ _ = j ≫ _
      calc
        _ = (j ≫ e.unitIso.hom.app ((relativeLatchingMapArrowFunctor (C := C) k).obj f).left) ≫
            e.inverse.map ((α.hom.app f).left) ≫ (β.hom.app fF).left := by
              simp only [Category.assoc]
        _ = (e.unitIso.hom.app (latchingObject f.right k) ≫ e.inverse.map (e.functor.map j)) ≫
            e.inverse.map ((α.hom.app f).left) ≫ (β.hom.app fF).left := by rw [hn]
        _ = e.unitIso.hom.app (latchingObject f.right k) ≫
            e.inverse.map (e.functor.map j ≫ (α.hom.app f).left) ≫ (β.hom.app fF).left := by
          simp only [Functor.map_comp, Category.assoc]
        _ = e.unitIso.hom.app (latchingObject f.right k) ≫
            e.inverse.map ((coefficientLatchingObjectIso e.functor k).hom.app f.right ≫
              relativeLatchingInr' k fF) ≫ (β.hom.app fF).left := by rw [hα]
        _ = (e.unitIso.hom.app (latchingObject f.right k) ≫
            e.inverse.map ((coefficientLatchingObjectIso e.functor k).hom.app f.right) ≫
            (coefficientLatchingObjectIso e.inverse k).hom.app fF.right) ≫
            relativeLatchingInr' k fGF := by
          rw [Functor.map_comp, Category.assoc, hβ]
          simp only [Category.assoc]
        _ = (latchingObjectFunctor k).map
            ((Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e).unitIso.hom.app f.right) ≫
            relativeLatchingInr' k fGF := by
          simpa only [fF, Arrow.mk_right] using congrArg (fun h => h ≫ relativeLatchingInr' k fGF)
            (coefficientLatchingObject_unit e k f.right)
        _ = _ := hh.symm
  · change e.unitIso.hom.app (f.right.obj (op ⦋k⦌)) ≫
        e.inverse.map ((α.hom.app f).right) ≫ (β.hom.app fF).right =
      ((B.unitIso.hom.app f).right).app (op ⦋k⦌)
    have hα : (α.hom.app f).right = 𝟙 (e.functor.obj (f.right.obj (op ⦋k⦌))) :=
      (coefficientRelativeLatching_equations e.functor k f.hom).2.2.2.2.1
    have hβ : (β.hom.app fF).right = 𝟙 (e.inverse.obj (fF.right.obj (op ⦋k⦌))) :=
      (coefficientRelativeLatching_equations e.inverse k fF.hom).2.2.2.2.1
    rw [hα, hβ]
    simp [fF, B, Functor.mapArrowEquivalence, Equivalence.congrRight]

end LatchingUnit

section LatchingCoherence

variable (e : C ≌ D) (k : ℕ)
variable [HasColimitsOfShape (latchingIndex k) C]
  [HasColimitsOfShape (latchingIndex k) D] [HasPushouts C] [HasPushouts D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRelativeLatching_mate :
    mateEquiv
        (Functor.mapArrowEquivalence (Equivalence.congrRight
            (E := SimplexCategoryᵒᵖ) e)).toAdjunction
        (Functor.mapArrowEquivalence e).toAdjunction
        (coefficientRelativeLatchingArrowIso e.functor k).hom =
      (coefficientRelativeLatchingArrowIso e.inverse k).inv := by
  let A := Functor.mapArrowEquivalence e
  let B := Functor.mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
  let QC := relativeLatchingMapArrowFunctor (C := C) k
  let QD := relativeLatchingMapArrowFunctor (C := D) k
  let α : QC ⋙ A.functor ≅ B.functor ⋙ QD := coefficientRelativeLatchingArrowIso e.functor k
  let β : QD ⋙ A.inverse ≅ B.inverse ⋙ QC := coefficientRelativeLatchingArrowIso e.inverse k
  apply NatTrans.ext
  funext g
  let x := B.inverse.obj g
  have hu : A.unitIso.hom.app (QC.obj x) ≫ A.inverse.map (α.hom.app x) =
      QC.map (B.unitIso.hom.app x) ≫ β.inv.app (B.functor.obj x) := by
    calc
      _ = (A.unitIso.hom.app (QC.obj x) ≫ A.inverse.map (α.hom.app x) ≫
          β.hom.app (B.functor.obj x)) ≫ β.inv.app (B.functor.obj x) := by
        simp only [Category.assoc, β.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
      _ = _ := by
        have hh : A.unitIso.hom.app (QC.obj x) ≫ A.inverse.map (α.hom.app x) ≫
            β.hom.app (B.functor.obj x) = QC.map (B.unitIso.hom.app x) :=
          coefficientRelativeLatching_unit_hom e k x
        exact congrArg (fun t => t ≫ β.inv.app (B.functor.obj x)) hh
  have hn : β.inv.app (B.functor.obj x) ≫ A.inverse.map (QD.map (B.counitIso.hom.app g)) =
      QC.map (B.inverse.map (B.counitIso.hom.app g)) ≫ β.inv.app g := by
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, x] using
      (β.inv.naturality (B.counitIso.hom.app g)).symm
  have ht : B.unitIso.hom.app x ≫ B.inverse.map (B.counitIso.hom.app g) = 𝟙 x :=
    B.unit_inverse_comp g
  calc
    (mateEquiv B.toAdjunction A.toAdjunction α.hom).app g =
        (A.unitIso.hom.app (QC.obj x) ≫ A.inverse.map (α.hom.app x)) ≫
          A.inverse.map (QD.map (B.counitIso.hom.app g)) := by
      simp [mateEquiv, Equivalence.toAdjunction, x, Category.assoc]
    _ = (QC.map (B.unitIso.hom.app x) ≫ β.inv.app (B.functor.obj x)) ≫
        A.inverse.map (QD.map (B.counitIso.hom.app g)) := by rw [hu]
    _ = QC.map (B.unitIso.hom.app x) ≫
        QC.map (B.inverse.map (B.counitIso.hom.app g)) ≫ β.inv.app g := by
      rw [Category.assoc, hn]
    _ = β.inv.app g := by
      rw [← Category.assoc, ← QC.map_comp, ht]
      calc
        QC.map (𝟙 x) ≫ β.inv.app g = (𝟙 (QC.obj x)) ≫ β.inv.app g :=
          congrArg (fun t => t ≫ β.inv.app g) (QC.map_id x)
        _ = β.inv.app g := by
          simpa only [Functor.comp_obj, x] using Category.id_comp (β.inv.app g)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The same coefficient constructions for an equivalence and its inverse satisfy the native
mate unit and counit equations on the whole relative latching arrows. -/
theorem coefficientRelativeLatching_unit_counit
    (f : Arrow (SimplicialObject C)) (g : Arrow (SimplicialObject D)) :
    let A := Functor.mapArrowEquivalence e
    let B := Functor.mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
    let QC := relativeLatchingMapArrowFunctor (C := C) k
    let QD := relativeLatchingMapArrowFunctor (C := D) k
    let α := coefficientRelativeLatchingArrowIso e.functor k
    let β := coefficientRelativeLatchingArrowIso e.inverse k
    (A.unitIso.app (QC.obj f) ≪≫ A.inverse.mapIso (α.app f) ≪≫ β.app (B.functor.obj f) =
      QC.mapIso (B.unitIso.app f)) ∧
    (A.functor.mapIso (β.app g) ≪≫ α.app (B.inverse.obj g) ≪≫ QD.mapIso (B.counitIso.app g) =
      A.counitIso.app (QD.obj g)) := by
  let A := Functor.mapArrowEquivalence e
  let B := Functor.mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
  let QC := relativeLatchingMapArrowFunctor (C := C) k
  let QD := relativeLatchingMapArrowFunctor (C := D) k
  let α : QC ⋙ A.functor ≅ B.functor ⋙ QD := coefficientRelativeLatchingArrowIso e.functor k
  let β : QD ⋙ A.inverse ≅ B.inverse ⋙ QC := coefficientRelativeLatchingArrowIso e.inverse k
  have hm : mateEquiv B.toAdjunction A.toAdjunction α.hom = β.inv :=
    coefficientRelativeLatching_mate e k
  constructor
  · apply Iso.ext
    change A.unitIso.hom.app (QC.obj f) ≫ A.inverse.map (α.hom.app f) ≫
        β.hom.app (B.functor.obj f) = QC.map (B.unitIso.hom.app f)
    have h := unit_mateEquiv B.toAdjunction A.toAdjunction α.hom f
    rw [hm] at h
    dsimp only [Equivalence.toAdjunction, Equivalence.unit, Equivalence.counit, Functor.id_obj] at h
    calc
      _ = (QC.map (B.unitIso.hom.app f) ≫ β.inv.app (B.functor.obj f)) ≫
          β.hom.app (B.functor.obj f) := by
        simpa only [Category.assoc] using
          congrArg (fun t => t ≫ β.hom.app (B.functor.obj f)) h.symm
      _ = _ := by simp only [Category.assoc, β.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  · apply Iso.ext
    change A.functor.map (β.hom.app g) ≫ α.hom.app (B.inverse.obj g) ≫
        QD.map (B.counitIso.hom.app g) = A.counitIso.hom.app (QD.obj g)
    have h := mateEquiv_counit B.toAdjunction A.toAdjunction α.hom g
    rw [hm] at h
    dsimp only [Equivalence.toAdjunction, Equivalence.unit, Equivalence.counit, Functor.id_obj] at h
    calc
      _ = A.functor.map (β.hom.app g) ≫
          (A.functor.map (β.inv.app g) ≫ A.counitIso.hom.app (QD.obj g)) := by
        simpa only [Category.assoc] using
          congrArg (fun t => A.functor.map (β.hom.app g) ≫ t) h.symm
      _ = _ := by
        rw [← Category.assoc, ← A.functor.map_comp, β.hom_inv_id_app,
          A.functor.map_id]
        simp only [Functor.comp_obj, Category.id_comp]

end LatchingCoherence

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientMatchingObject_unit (e : C ≌ D) (k : ℕ)
    [HasLimitsOfShape (matchingIndex k) C]
    [HasLimitsOfShape (matchingIndex k) D]
    (X : SimplicialObject C) :
    e.unitIso.hom.app (matchingObject X k) ≫
        e.inverse.map ((coefficientMatchingObjectIso e.functor k).hom.app X) ≫
        (coefficientMatchingObjectIso e.inverse k).hom.app (X ⋙ e.functor) =
      (matchingObjectFunctor k).map
        ((Equivalence.congrRight e).unitIso.hom.app X) := by
  apply limit.hom_ext
  intro a
  change
    (e.unitIso.hom.app (matchingObject X k) ≫
        e.inverse.map ((coefficientMatchingObjectIso e.functor k).hom.app X) ≫
        (coefficientMatchingObjectIso e.inverse k).hom.app (X ⋙ e.functor)) ≫
        matchingπ ((X ⋙ e.functor) ⋙ e.inverse) k a =
      (matchingObjectFunctor k).map
          ((Equivalence.congrRight e).unitIso.hom.app X) ≫
        matchingπ ((X ⋙ e.functor) ⋙ e.inverse) k a
  have hunit : e.unitIso.hom.app (matchingObject X k) ≫
      e.inverse.map (e.functor.map (matchingπ X k a)) =
        matchingπ X k a ≫ e.unitIso.hom.app (X.obj a.obj.right) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (e.unitIso.hom.naturality (matchingπ X k a)).symm
  simp only [Category.assoc]
  rw [(coefficientMatchingObject_legs e.inverse k (X ⋙ e.functor) a).1,
    ← e.inverse.map_comp,
    (coefficientMatchingObject_legs e.functor k X a).1, hunit]
  simpa [Equivalence.congrRight] using
    (matchingObjectFunctor_map_π k
      ((Equivalence.congrRight e).unitIso.hom.app X) a).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRelativeMatching_unit_hom (e : C ≌ D) (k : ℕ)
    [HasLimitsOfShape (matchingIndex k) C]
    [HasLimitsOfShape (matchingIndex k) D]
    [HasPullbacks C] [HasPullbacks D]
    (f : Arrow (SimplicialObject C)) :
    let A := mapArrowEquivalence e
    let B := mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
    let αM := coefficientRelativeMatchingArrowIso e.functor k
    let βM := coefficientRelativeMatchingArrowIso e.inverse k
    A.unitIso.hom.app ((relativeMatchingMapArrowFunctor (C := C) k).obj f) ≫
        A.inverse.map ((αM.app f).hom) ≫
        (βM.app (B.functor.obj f)).hom =
      (relativeMatchingMapArrowFunctor (C := C) k).map (B.unitIso.hom.app f) := by
  dsimp only
  let fF := Arrow.mk (whiskerRight f.hom e.functor)
  let fFG := Arrow.mk (whiskerRight (whiskerRight f.hom e.functor) e.inverse)
  let α := (coefficientRelativeMatchingArrowIso e.functor k).app f
  let β := (coefficientRelativeMatchingArrowIso e.inverse k).app fF
  let a : e.functor.obj (relativeMatchingObject f.hom k) ⟶
      relativeMatchingObject fF.hom k := α.hom.right
  let b : e.inverse.obj (relativeMatchingObject fF.hom k) ⟶
      relativeMatchingObject fFG.hom k := β.hom.right
  let al : e.functor.obj (f.left.obj (op ⦋k⦌)) ⟶
      e.functor.obj (f.left.obj (op ⦋k⦌)) := α.hom.left
  let bl : e.inverse.obj (e.functor.obj (f.left.obj (op ⦋k⦌))) ⟶
      e.inverse.obj (e.functor.obj (f.left.obj (op ⦋k⦌))) := β.hom.left
  let q : f ⟶ fFG :=
    (mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)).unitIso.hom.app f
  let r : relativeMatchingObject f.hom k ⟶ relativeMatchingObject fFG.hom k :=
    ((relativeMatchingMapArrowFunctor k).map q).right
  have hαfst : a ≫
      pullback.fst (matchingMap fF.right k) ((matchingObjectFunctor k).map fF.hom) =
        e.functor.map
          (pullback.fst (matchingMap f.right k) ((matchingObjectFunctor k).map f.hom)) :=
    (coefficientRelativeMatching_equations e.functor k f.hom).1
  have hαsnd : a ≫
      pullback.snd (matchingMap fF.right k) ((matchingObjectFunctor k).map fF.hom) =
        e.functor.map
            (pullback.snd (matchingMap f.right k) ((matchingObjectFunctor k).map f.hom)) ≫
          (coefficientMatchingObjectIso e.functor k).hom.app f.left :=
    (coefficientRelativeMatching_equations e.functor k f.hom).2.1
  have hβfst : b ≫
      pullback.fst (matchingMap fFG.right k) ((matchingObjectFunctor k).map fFG.hom) =
        e.inverse.map
          (pullback.fst (matchingMap fF.right k) ((matchingObjectFunctor k).map fF.hom)) :=
    (coefficientRelativeMatching_equations e.inverse k fF.hom).1
  have hβsnd : b ≫
      pullback.snd (matchingMap fFG.right k) ((matchingObjectFunctor k).map fFG.hom) =
        e.inverse.map
            (pullback.snd (matchingMap fF.right k) ((matchingObjectFunctor k).map fF.hom)) ≫
          (coefficientMatchingObjectIso e.inverse k).hom.app fF.left :=
    (coefficientRelativeMatching_equations e.inverse k fF.hom).2.1
  have hαleft : al = 𝟙 (e.functor.obj (f.left.obj (op ⦋k⦌))) :=
    (coefficientRelativeMatching_equations e.functor k f.hom).2.2.2.2.1
  have hβleft : bl = 𝟙 (e.inverse.obj (e.functor.obj (f.left.obj (op ⦋k⦌)))) :=
    (coefficientRelativeMatching_equations e.inverse k fF.hom).2.2.2.2.1
  have hrfst : r ≫
      pullback.fst (matchingMap fFG.right k) ((matchingObjectFunctor k).map fFG.hom) =
        pullback.fst (matchingMap f.right k) ((matchingObjectFunctor k).map f.hom) ≫
          e.unitIso.hom.app (f.right.obj (op ⦋k⦌)) := by
    simpa [r, q, fF, fFG, mapArrowEquivalence, Equivalence.congrRight] using
      (relativeMatchingMapArrowFunctor_map_right_fst k q)
  have hrsnd : r ≫
      pullback.snd (matchingMap fFG.right k) ((matchingObjectFunctor k).map fFG.hom) =
        pullback.snd (matchingMap f.right k) ((matchingObjectFunctor k).map f.hom) ≫
          (matchingObjectFunctor k).map
            ((Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e).unitIso.hom.app f.left) := by
    simpa [r, q, fF, fFG, mapArrowEquivalence] using
      (relativeMatchingMapArrowFunctor_map_right_snd k q)
  apply Arrow.hom_ext
  · change e.unitIso.hom.app (f.left.obj (op ⦋k⦌)) ≫
      e.inverse.map al ≫ bl = q.left.app (op ⦋k⦌)
    simp [hαleft, hβleft, q, mapArrowEquivalence, Equivalence.congrRight]
  · change e.unitIso.hom.app (relativeMatchingObject f.hom k) ≫
      e.inverse.map a ≫ b = r
    apply pullback.hom_ext
    · change (e.unitIso.hom.app (relativeMatchingObject f.hom k) ≫
          e.inverse.map a ≫ b) ≫
          pullback.fst (matchingMap fFG.right k) ((matchingObjectFunctor k).map fFG.hom) = _
      simp only [Category.assoc]
      rw [hβfst, ← e.inverse.map_comp, hαfst]
      have hunit := (e.unitIso.hom.naturality
        (pullback.fst (matchingMap f.right k)
          ((matchingObjectFunctor k).map f.hom))).symm
      simp only [Functor.id_map, Functor.comp_map] at hunit
      rw [hunit]
      exact hrfst.symm
    · change (e.unitIso.hom.app (relativeMatchingObject f.hom k) ≫
          e.inverse.map a ≫ b) ≫
          pullback.snd (matchingMap fFG.right k) ((matchingObjectFunctor k).map fFG.hom) = _
      simp only [Category.assoc]
      rw [hβsnd, ← Category.assoc (e.inverse.map a),
        ← e.inverse.map_comp, hαsnd, e.inverse.map_comp]
      have hunit := (e.unitIso.hom.naturality
        (pullback.snd (matchingMap f.right k)
          ((matchingObjectFunctor k).map f.hom))).symm
      simp only [Functor.id_map, Functor.comp_map] at hunit
      calc
        _ = (pullback.snd (matchingMap f.right k)
              ((matchingObjectFunctor k).map f.hom) ≫
              e.unitIso.hom.app (matchingObject f.left k)) ≫
            e.inverse.map ((coefficientMatchingObjectIso e.functor k).hom.app f.left) ≫
            (coefficientMatchingObjectIso e.inverse k).hom.app fF.left := by
          simpa only [Category.assoc] using
            congrArg (fun t => t ≫
              e.inverse.map ((coefficientMatchingObjectIso e.functor k).hom.app f.left) ≫
              (coefficientMatchingObjectIso e.inverse k).hom.app fF.left) hunit
        _ = pullback.snd (matchingMap f.right k)
              ((matchingObjectFunctor k).map f.hom) ≫
            (matchingObjectFunctor k).map
              ((Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e).unitIso.hom.app f.left) := by
          simpa only [Category.assoc, fF, Arrow.mk_left] using
            congrArg (fun t => pullback.snd (matchingMap f.right k)
              ((matchingObjectFunctor k).map f.hom) ≫ t)
              (coefficientMatchingObject_unit e k f.left)
        _ = _ := hrsnd.symm


section MatchingCoherence

variable (e : C ≌ D) (k : ℕ)
variable [HasLimitsOfShape (matchingIndex k) C]
  [HasLimitsOfShape (matchingIndex k) D] [HasPullbacks C] [HasPullbacks D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRelativeMatching_mate :
    mateEquiv
        (Functor.mapArrowEquivalence (Equivalence.congrRight
            (E := SimplexCategoryᵒᵖ) e)).toAdjunction
        (Functor.mapArrowEquivalence e).toAdjunction
        (coefficientRelativeMatchingArrowIso e.functor k).hom =
      (coefficientRelativeMatchingArrowIso e.inverse k).inv := by
  let A := Functor.mapArrowEquivalence e
  let B := Functor.mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
  let QC := relativeMatchingMapArrowFunctor (C := C) k
  let QD := relativeMatchingMapArrowFunctor (C := D) k
  let α : QC ⋙ A.functor ≅ B.functor ⋙ QD := coefficientRelativeMatchingArrowIso e.functor k
  let β : QD ⋙ A.inverse ≅ B.inverse ⋙ QC := coefficientRelativeMatchingArrowIso e.inverse k
  apply NatTrans.ext
  funext g
  let x := B.inverse.obj g
  have hu : A.unitIso.hom.app (QC.obj x) ≫ A.inverse.map (α.hom.app x) =
      QC.map (B.unitIso.hom.app x) ≫ β.inv.app (B.functor.obj x) := by
    calc
      _ = (A.unitIso.hom.app (QC.obj x) ≫ A.inverse.map (α.hom.app x) ≫
          β.hom.app (B.functor.obj x)) ≫ β.inv.app (B.functor.obj x) := by
        simp only [Category.assoc, β.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
      _ = _ := by
        have hh : A.unitIso.hom.app (QC.obj x) ≫ A.inverse.map (α.hom.app x) ≫
            β.hom.app (B.functor.obj x) = QC.map (B.unitIso.hom.app x) :=
          coefficientRelativeMatching_unit_hom e k x
        exact congrArg (fun t => t ≫ β.inv.app (B.functor.obj x)) hh
  have hn : β.inv.app (B.functor.obj x) ≫ A.inverse.map (QD.map (B.counitIso.hom.app g)) =
      QC.map (B.inverse.map (B.counitIso.hom.app g)) ≫ β.inv.app g := by
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, x] using
      (β.inv.naturality (B.counitIso.hom.app g)).symm
  have ht : B.unitIso.hom.app x ≫ B.inverse.map (B.counitIso.hom.app g) = 𝟙 x :=
    B.unit_inverse_comp g
  calc
    (mateEquiv B.toAdjunction A.toAdjunction α.hom).app g =
        (A.unitIso.hom.app (QC.obj x) ≫ A.inverse.map (α.hom.app x)) ≫
          A.inverse.map (QD.map (B.counitIso.hom.app g)) := by
      simp [mateEquiv, Equivalence.toAdjunction, x, Category.assoc]
    _ = (QC.map (B.unitIso.hom.app x) ≫ β.inv.app (B.functor.obj x)) ≫
        A.inverse.map (QD.map (B.counitIso.hom.app g)) := by rw [hu]
    _ = QC.map (B.unitIso.hom.app x) ≫
        QC.map (B.inverse.map (B.counitIso.hom.app g)) ≫ β.inv.app g := by
      rw [Category.assoc, hn]
    _ = β.inv.app g := by
      rw [← Category.assoc, ← QC.map_comp, ht]
      calc
        QC.map (𝟙 x) ≫ β.inv.app g = (𝟙 (QC.obj x)) ≫ β.inv.app g :=
          congrArg (fun t => t ≫ β.inv.app g) (QC.map_id x)
        _ = β.inv.app g := by
          simpa only [Functor.comp_obj, x] using Category.id_comp (β.inv.app g)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The same coefficient constructions for an equivalence and its inverse satisfy the native
mate unit and counit equations on the whole relative matching arrows. -/
theorem coefficientRelativeMatching_unit_counit
    (f : Arrow (SimplicialObject C)) (g : Arrow (SimplicialObject D)) :
    let A := Functor.mapArrowEquivalence e
    let B := Functor.mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
    let QC := relativeMatchingMapArrowFunctor (C := C) k
    let QD := relativeMatchingMapArrowFunctor (C := D) k
    let α := coefficientRelativeMatchingArrowIso e.functor k
    let β := coefficientRelativeMatchingArrowIso e.inverse k
    (A.unitIso.app (QC.obj f) ≪≫ A.inverse.mapIso (α.app f) ≪≫ β.app (B.functor.obj f) =
      QC.mapIso (B.unitIso.app f)) ∧
    (A.functor.mapIso (β.app g) ≪≫ α.app (B.inverse.obj g) ≪≫ QD.mapIso (B.counitIso.app g) =
      A.counitIso.app (QD.obj g)) := by
  let A := Functor.mapArrowEquivalence e
  let B := Functor.mapArrowEquivalence (Equivalence.congrRight (E := SimplexCategoryᵒᵖ) e)
  let QC := relativeMatchingMapArrowFunctor (C := C) k
  let QD := relativeMatchingMapArrowFunctor (C := D) k
  let α : QC ⋙ A.functor ≅ B.functor ⋙ QD := coefficientRelativeMatchingArrowIso e.functor k
  let β : QD ⋙ A.inverse ≅ B.inverse ⋙ QC := coefficientRelativeMatchingArrowIso e.inverse k
  have hm : mateEquiv B.toAdjunction A.toAdjunction α.hom = β.inv :=
    coefficientRelativeMatching_mate e k
  constructor
  · apply Iso.ext
    change A.unitIso.hom.app (QC.obj f) ≫ A.inverse.map (α.hom.app f) ≫
        β.hom.app (B.functor.obj f) = QC.map (B.unitIso.hom.app f)
    have h := unit_mateEquiv B.toAdjunction A.toAdjunction α.hom f
    rw [hm] at h
    dsimp only [Equivalence.toAdjunction, Equivalence.unit, Equivalence.counit, Functor.id_obj] at h
    calc
      _ = (QC.map (B.unitIso.hom.app f) ≫ β.inv.app (B.functor.obj f)) ≫
          β.hom.app (B.functor.obj f) := by
        simpa only [Category.assoc] using
          congrArg (fun t => t ≫ β.hom.app (B.functor.obj f)) h.symm
      _ = _ := by simp only [Category.assoc, β.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  · apply Iso.ext
    change A.functor.map (β.hom.app g) ≫ α.hom.app (B.inverse.obj g) ≫
        QD.map (B.counitIso.hom.app g) = A.counitIso.hom.app (QD.obj g)
    have h := mateEquiv_counit B.toAdjunction A.toAdjunction α.hom g
    rw [hm] at h
    dsimp only [Equivalence.toAdjunction, Equivalence.unit, Equivalence.counit, Functor.id_obj] at h
    calc
      _ = A.functor.map (β.hom.app g) ≫
          (A.functor.map (β.inv.app g) ≫ A.counitIso.hom.app (QD.obj g)) := by
        simpa only [Category.assoc] using
          congrArg (fun t => A.functor.map (β.hom.app g) ≫ t) h.symm
      _ = _ := by
        rw [← Category.assoc, ← A.functor.map_comp, β.hom_inv_id_app,
          A.functor.map_id]
        simp only [Functor.comp_obj, Category.id_comp]

end MatchingCoherence

end CategoryTheory.SimplicialObject
