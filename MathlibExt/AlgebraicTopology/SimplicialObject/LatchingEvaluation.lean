/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.CoefficientPreservation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Relative latching arrows and coefficient evaluation

The evaluation comparison is the specialization of the generic coefficient
comparison. Its characteristic equations use the same chosen colimit and
pushout. Naturality in the coefficient index is the additional evaluation law.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
variable [HasPushouts C]

/-- The relative latching comparison is the actual evaluation specialization
of the generic coefficient comparison, with the same chosen maps. -/
def relativeLatchingMapEvaluationIso (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C] :
    relativeLatchingMapArrowFunctor (C := J ⥤ C) k ⋙
        ((evaluation J C).obj j).mapArrow ≅
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).obj
        ((evaluation J C).obj j)).mapArrow ⋙ relativeLatchingMapArrowFunctor (C := C) k :=
  coefficientRelativeLatchingArrowIso ((evaluation J C).obj j) k

/-- Both APIs use exactly the same whole-arrow comparison. -/
theorem relativeLatchingMapEvaluationIso_eq_coefficient (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C] :
    relativeLatchingMapEvaluationIso j k =
      coefficientRelativeLatchingArrowIso ((evaluation J C).obj j) k := rfl

omit [HasPushouts C] in
private theorem evaluationLatchingIso_eq (X : SimplicialObject (J ⥤ C))
    (j : J) (k : ℕ) [HasColimitsOfShape (latchingIndex k) C] :
    (coefficientLatchingObjectIso ((evaluation J C).obj j) k).hom.app X =
      (colimitObjIsoColimitCompEvaluation (latchingDiagram X k) j).hom := rfl

omit [HasPushouts C] in
private theorem evaluationLatchingIso_inv (X : SimplicialObject (J ⥤ C))
    (j : J) (k : ℕ) [HasColimitsOfShape (latchingIndex k) C] :
    (coefficientLatchingObjectIso ((evaluation J C).obj j) k).inv.app X =
      (colimitObjIsoColimitCompEvaluation (latchingDiagram X k) j).inv := rfl

/-- The target component is the identity of the original evaluated target. -/
@[simp]
theorem relativeLatchingMapEvaluationIso_hom_right (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    {X Y : SimplicialObject (J ⥤ C)} (f : X ⟶ Y) :
    ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).right =
      𝟙 ((Y.obj (op ⦋k⦌)).obj j) := by
  exact (coefficientRelativeLatching_equations ((evaluation J C).obj j) k f).2.2.2.2.1

/-- The inverse target component retains that same identity. -/
@[simp]
theorem relativeLatchingMapEvaluationIso_inv_right (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    {X Y : SimplicialObject (J ⥤ C)} (f : X ⟶ Y) :
    ((relativeLatchingMapEvaluationIso j k).inv.app (Arrow.mk f)).right =
      𝟙 ((Y.obj (op ⦋k⦌)).obj j) := by
  exact (coefficientRelativeLatching_equations ((evaluation J C).obj j) k f).2.2.2.2.2

/-- The original ordinary-source pushout injection is preserved by the forward comparison. -/
@[reassoc]
theorem relativeLatchingMapEvaluationIso_hom_left_inl (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    {X Y : SimplicialObject (J ⥤ C)} (f : X ⟶ Y) :
    (pushout.inl (latchingMap X k) ((latchingObjectFunctor k).map f)).app j ≫
        ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).left =
      pushout.inl (latchingMap (X ⋙ (evaluation J C).obj j) k)
        ((latchingObjectFunctor k).map (Functor.whiskerRight f ((evaluation J C).obj j))) := by
  exact (coefficientRelativeLatching_equations ((evaluation J C).obj j) k f).1

/-- The original latching-target injection is preserved through the native colimit comparison. -/
@[reassoc]
theorem relativeLatchingMapEvaluationIso_hom_left_inr (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    {X Y : SimplicialObject (J ⥤ C)} (f : X ⟶ Y) :
    (pushout.inr (latchingMap X k) ((latchingObjectFunctor k).map f)).app j ≫
        ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).left =
      (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j).hom ≫
        pushout.inr (latchingMap (X ⋙ (evaluation J C).obj j) k)
          ((latchingObjectFunctor k).map
            (Functor.whiskerRight f ((evaluation J C).obj j))) := by
  have h := (coefficientRelativeLatching_equations ((evaluation J C).obj j) k f).2.1
  rw [evaluationLatchingIso_eq] at h
  exact h

/-- The inverse comparison recovers the original ordinary-source injection. -/
@[reassoc]
theorem relativeLatchingMapEvaluationIso_inv_left_inl (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    {X Y : SimplicialObject (J ⥤ C)} (f : X ⟶ Y) :
    pushout.inl (latchingMap (X ⋙ (evaluation J C).obj j) k)
        ((latchingObjectFunctor k).map (Functor.whiskerRight f ((evaluation J C).obj j))) ≫
          ((relativeLatchingMapEvaluationIso j k).inv.app (Arrow.mk f)).left =
      (pushout.inl (latchingMap X k) ((latchingObjectFunctor k).map f)).app j := by
  exact (coefficientRelativeLatching_equations ((evaluation J C).obj j) k f).2.2.1

/-- The inverse comparison recovers the latching-target injection through the same colimit iso. -/
@[reassoc]
theorem relativeLatchingMapEvaluationIso_inv_left_inr (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    {X Y : SimplicialObject (J ⥤ C)} (f : X ⟶ Y) :
    pushout.inr (latchingMap (X ⋙ (evaluation J C).obj j) k)
        ((latchingObjectFunctor k).map (Functor.whiskerRight f ((evaluation J C).obj j))) ≫
          ((relativeLatchingMapEvaluationIso j k).inv.app (Arrow.mk f)).left =
      (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j).inv ≫
        (pushout.inr (latchingMap X k) ((latchingObjectFunctor k).map f)).app j := by
  have h := (coefficientRelativeLatching_equations ((evaluation J C).obj j) k f).2.2.2.1
  rw [evaluationLatchingIso_inv] at h
  exact h

/-- The comparison preserves the original relative latching structure map. -/
theorem relativeLatchingMapEvaluationIso_hom_map (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    {X Y : SimplicialObject (J ⥤ C)} (f : X ⟶ Y) :
    (relativeLatchingMap f k).app j =
      ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).left ≫
        relativeLatchingMap (Functor.whiskerRight f ((evaluation J C).obj j)) k := by
  have h := ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).w
  change _ ≫ relativeLatchingMap (Functor.whiskerRight f ((evaluation J C).obj j)) k =
    (relativeLatchingMap f k).app j ≫ _ at h
  rw [relativeLatchingMapEvaluationIso_hom_right, Category.comp_id] at h
  exact h.symm

/-- The inverse comparison recovers the original relative latching structure map. -/
theorem relativeLatchingMapEvaluationIso_inv_map (j : J) (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    {X Y : SimplicialObject (J ⥤ C)} (f : X ⟶ Y) :
    relativeLatchingMap (Functor.whiskerRight f ((evaluation J C).obj j)) k =
      ((relativeLatchingMapEvaluationIso j k).inv.app (Arrow.mk f)).left ≫
        (relativeLatchingMap f k).app j := by
  have h := ((relativeLatchingMapEvaluationIso j k).inv.app (Arrow.mk f)).w
  change _ ≫ (relativeLatchingMap f k).app j =
    relativeLatchingMap (Functor.whiskerRight f ((evaluation J C).obj j)) k ≫ _ at h
  rw [relativeLatchingMapEvaluationIso_inv_right] at h
  exact (h.trans (Category.comp_id _)).symm


private abbrev ev (j : J) : (J ⥤ C) ⥤ C := (evaluation J C).obj j

set_option backward.isDefEq.respectTransparency false in
private theorem evaluationRelative_index {X Y : SimplicialObject (J ⥤ C)}
    (f : X ⟶ Y) {j j' : J} (a : j ⟶ j') (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C] :
    (relativeLatchingObject f k).map a ≫
        ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left =
      ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).left ≫
        ((relativeLatchingMapArrowFunctor (C := C) k).map
          (((Functor.mapArrowFunctor (SimplicialObject (J ⥤ C)) (SimplicialObject C)).map
            ((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).map
              ((evaluation J C).map a))).app (Arrow.mk f))).left := by
  let qj : Arrow.mk (Functor.whiskerRight f (ev j)) ⟶
      Arrow.mk (Functor.whiskerRight f (ev j')) :=
    ((Functor.mapArrowFunctor (SimplicialObject (J ⥤ C)) (SimplicialObject C)).map
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).map
        ((evaluation J C).map a))).app (Arrow.mk f)
  let rj : relativeLatchingObject (Functor.whiskerRight f (ev j)) k ⟶
      relativeLatchingObject (Functor.whiskerRight f (ev j')) k :=
    ((relativeLatchingMapArrowFunctor k).map qj).left
  change (relativeLatchingObject f k).map a ≫
      ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left =
    ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).left ≫ rj
  apply
      (cancel_epi (PreservesPushout.iso (ev j) (latchingMap X k)
        ((latchingObjectFunctor k).map f)).hom).mp
  apply pushout.hom_ext
  · have hr : (pushout.inl (latchingMap X k) ((latchingObjectFunctor k).map f)).app j ≫
          (relativeLatchingObject f k).map a =
        (X.obj (op ⦋k⦌)).map a ≫
          (pushout.inl (latchingMap X k) ((latchingObjectFunctor k).map f)).app j' :=
      (pushout.inl (latchingMap X k) ((latchingObjectFunctor k).map f)).naturality a |>.symm
    have hrj : pushout.inl (latchingMap (X ⋙ ev j) k)
          ((latchingObjectFunctor k).map (Functor.whiskerRight f (ev j))) ≫ rj =
        (X.obj (op ⦋k⦌)).map a ≫
          pushout.inl (latchingMap (X ⋙ ev j') k)
            ((latchingObjectFunctor k).map (Functor.whiskerRight f (ev j'))) :=
      relativeLatchingMapArrowFunctor_map_left_inl k qj
    calc
      _ = (pushout.inl (latchingMap X k) ((latchingObjectFunctor k).map f)).app j ≫
          (relativeLatchingObject f k).map a ≫
              ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left := by
        simpa only [Category.assoc, ev, evaluation,
          CategoryTheory.Functor.obj, CategoryTheory.Functor.map] using congrArg
          (fun z => z ≫ (relativeLatchingObject f k).map a ≫
            ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left)
                (PreservesPushout.inl_iso_hom (ev j) (latchingMap X k)
                  ((latchingObjectFunctor k).map f))
      _ = (X.obj (op ⦋k⦌)).map a ≫
          (pushout.inl (latchingMap X k) ((latchingObjectFunctor k).map f)).app j' ≫
            ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left := by
        simpa only [Category.assoc] using
          congrArg
              (fun z => z ≫
                ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left) hr
      _ = (X.obj (op ⦋k⦌)).map a ≫
          pushout.inl (latchingMap (X ⋙ ev j') k)
            ((latchingObjectFunctor k).map (Functor.whiskerRight f (ev j'))) := by
        rw [relativeLatchingMapEvaluationIso_hom_left_inl]
      _ = pushout.inl (latchingMap (X ⋙ ev j) k)
          ((latchingObjectFunctor k).map (Functor.whiskerRight f (ev j))) ≫ rj := hrj.symm
      _ = (pushout.inl (latchingMap X k) ((latchingObjectFunctor k).map f)).app j ≫
          ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).left ≫ rj := by
        simpa only [Category.assoc] using
          congrArg (fun z => z ≫ rj) (relativeLatchingMapEvaluationIso_hom_left_inl j k f).symm
      _ = _ := by
        simpa only [Category.assoc, ev, evaluation,
          CategoryTheory.Functor.obj, CategoryTheory.Functor.map] using congrArg
          (fun z => z ≫ ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).left ≫ rj)
          (PreservesPushout.inl_iso_hom (ev j) (latchingMap X k)
              ((latchingObjectFunctor k).map f)).symm
  · have hr : (pushout.inr (latchingMap X k) ((latchingObjectFunctor k).map f)).app j ≫
          (relativeLatchingObject f k).map a =
        (latchingObject Y k).map a ≫
          (pushout.inr (latchingMap X k) ((latchingObjectFunctor k).map f)).app j' :=
      (pushout.inr (latchingMap X k) ((latchingObjectFunctor k).map f)).naturality a |>.symm
    have hrj : pushout.inr (latchingMap (X ⋙ ev j) k)
          ((latchingObjectFunctor k).map (Functor.whiskerRight f (ev j))) ≫ rj =
        (latchingObjectFunctor k).map
            (((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).map
              ((evaluation J C).map a)).app Y) ≫
          pushout.inr (latchingMap (X ⋙ ev j') k)
            ((latchingObjectFunctor k).map (Functor.whiskerRight f (ev j'))) :=
      relativeLatchingMapArrowFunctor_map_left_inr k qj
    calc
      _ = (pushout.inr (latchingMap X k) ((latchingObjectFunctor k).map f)).app j ≫
          (relativeLatchingObject f k).map a ≫
              ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left := by
        simpa only [Category.assoc, ev, evaluation,
          CategoryTheory.Functor.obj, CategoryTheory.Functor.map] using congrArg
          (fun z => z ≫ (relativeLatchingObject f k).map a ≫
            ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left)
                (PreservesPushout.inr_iso_hom (ev j) (latchingMap X k)
                  ((latchingObjectFunctor k).map f))
      _ = (latchingObject Y k).map a ≫
          (pushout.inr (latchingMap X k) ((latchingObjectFunctor k).map f)).app j' ≫
            ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left := by
        simpa only [Category.assoc] using
          congrArg
              (fun z => z ≫
                ((relativeLatchingMapEvaluationIso j' k).hom.app (Arrow.mk f)).left) hr
      _ = (latchingObject Y k).map a ≫
          (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j').hom ≫
          pushout.inr (latchingMap (X ⋙ ev j') k)
            ((latchingObjectFunctor k).map (Functor.whiskerRight f (ev j'))) := by
        rw [relativeLatchingMapEvaluationIso_hom_left_inr]
      _ = (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j).hom ≫
          (latchingObjectFunctor k).map
            (((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).map
              ((evaluation J C).map a)).app Y) ≫
          pushout.inr (latchingMap (X ⋙ ev j') k)
            ((latchingObjectFunctor k).map (Functor.whiskerRight f (ev j'))) := by
        have h := colimit_map_colimitObjIsoColimitCompEvaluation_hom (latchingDiagram Y k) a
        change (latchingObject Y k).map a ≫
            (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j').hom =
          (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j).hom ≫
            (latchingObjectFunctor k).map
              (((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).map
                ((evaluation J C).map a)).app Y) at h
        change (latchingObject Y k).map a ≫
            (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j').hom ≫ _ =
          (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j).hom ≫
            (latchingObjectFunctor k).map
              (((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).map
                ((evaluation J C).map a)).app Y) ≫ _
        rw [← Category.assoc, h, Category.assoc]
      _ = (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j).hom ≫
          pushout.inr (latchingMap (X ⋙ ev j) k)
            ((latchingObjectFunctor k).map (Functor.whiskerRight f (ev j))) ≫ rj := by
        simpa only [Category.assoc] using
          congrArg
              (fun z =>
                (colimitObjIsoColimitCompEvaluation (latchingDiagram Y k) j).hom ≫ z) hrj.symm
      _ = (pushout.inr (latchingMap X k) ((latchingObjectFunctor k).map f)).app j ≫
          ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).left ≫ rj := by
        simpa only [Category.assoc] using
          congrArg (fun z => z ≫ rj) (relativeLatchingMapEvaluationIso_hom_left_inr j k f).symm
      _ = _ := by
        simpa only [Category.assoc, ev, evaluation,
          CategoryTheory.Functor.obj, CategoryTheory.Functor.map] using congrArg
          (fun z => z ≫ ((relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk f)).left ≫ rj)
          (PreservesPushout.inr_iso_hom (ev j) (latchingMap X k)
              ((latchingObjectFunctor k).map f)).symm


/-- The same whole-arrow comparison is compatible with every coefficient-index map. -/
theorem relativeLatchingMapEvaluationIso_hom_index {j j' : J} (a : j ⟶ j') (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    (f : Arrow (SimplicialObject (J ⥤ C))) :
    ((Functor.mapArrowFunctor (J ⥤ C) C).map ((evaluation J C).map a)).app
          ((relativeLatchingMapArrowFunctor k).obj f) ≫
        (relativeLatchingMapEvaluationIso j' k).hom.app f =
      (relativeLatchingMapEvaluationIso j k).hom.app f ≫
        (relativeLatchingMapArrowFunctor (C := C) k).map
          (((Functor.mapArrowFunctor (SimplicialObject (J ⥤ C)) (SimplicialObject C)).map
            ((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).map
              ((evaluation J C).map a))).app f) := by
  apply Arrow.hom_ext
  · exact evaluationRelative_index f.hom a k
  · change (f.right.obj (op ⦋k⦌)).map a ≫ 𝟙 _ =
      𝟙 _ ≫ (f.right.obj (op ⦋k⦌)).map a
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of that same comparison retains coefficient-index compatibility. -/
theorem relativeLatchingMapEvaluationIso_inv_index {j j' : J} (a : j ⟶ j') (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    (f : Arrow (SimplicialObject (J ⥤ C))) :
    (relativeLatchingMapArrowFunctor (C := C) k).map
          (((Functor.mapArrowFunctor (SimplicialObject (J ⥤ C)) (SimplicialObject C)).map
            ((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).map
              ((evaluation J C).map a))).app f) ≫
        (relativeLatchingMapEvaluationIso j' k).inv.app f =
      (relativeLatchingMapEvaluationIso j k).inv.app f ≫
        ((Functor.mapArrowFunctor (J ⥤ C) C).map ((evaluation J C).map a)).app
          ((relativeLatchingMapArrowFunctor k).obj f) := by
  apply (cancel_mono ((relativeLatchingMapEvaluationIso j' k).hom.app f)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [relativeLatchingMapEvaluationIso_hom_index]
  simp

end CategoryTheory.SimplicialObject
