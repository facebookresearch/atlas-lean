/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerTensorHom
import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# The whole inner Leibniz–Hom comparison

For a supplied pushout-product square, the original contravariant mapping end
is isomorphic, as an arrow, to the scalar pullback-Hom arrow. Both original
pushout injections, all four forward/inverse projections and every target
map are retained. This is model-free tensor–Hom geometry underlying Rezk,
* A model for the homotopy theory of homotopy theory *, Sections 2.5 and 9.1.
The proof uses the native parametrized adjunction and pullback universal
properties, together with the existing natural tensor–mapping isomorphism.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open scoped SimplicialSpace.Inner
namespace SimplicialSpace

private abbrev mapSpace (X Z : SimplicialSpace.{u}) : SSet.{u} :=
  (innerHomFunctor.{u}.obj (op X)).obj Z

private abbrev tensorHomIso (K : SSet.{u}) (X Z : SimplicialSpace.{u}) :
    mapSpace ((innerTensor K).obj X) Z ≅ (ihom K).obj (mapSpace X Z) :=
  (innerTensorHomIso K X).app Z

private abbrev restriction {A B : SimplicialSpace.{u}} (s : A ⟶ B)
    (Z : SimplicialSpace.{u}) : mapSpace B Z ⟶ mapSpace A Z :=
  (innerHomFunctor.{u}.map s.op).app Z

private abbrev scalarSquare {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialSpace.{u}) :=
  Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j (restriction s Z)

private lemma flipInnerHom_preservesPullbacks (Z : SimplicialSpace.{u}) :
    PreservesLimitsOfShape WalkingCospan (innerHomFunctor.{u}.flip.obj Z) := by
  let _ : ∀ K : SSet.{u}, PreservesColimitsOfShape WalkingCospanᵒᵖ
      (innerTensorBifunctor.{u}.flip.obj K) := fun K => by
    change PreservesColimitsOfShape WalkingCospanᵒᵖ (innerTensor K)
    let _ : (innerTensor K).IsLeftAdjoint :=
      (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  exact innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj WalkingCospan Z

private lemma mappedInnerPushout {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    IsPullback
      ((innerHomFunctor.{u}.map pp.inl.op).app Z)
      ((innerHomFunctor.{u}.map pp.inr.op).app Z)
      ((innerHomFunctor.{u}.map ((innerTensorBifunctor.{u}.map s).app K).op).app Z)
      ((innerHomFunctor.{u}.map ((innerTensorBifunctor.{u}.obj A).map j).op).app Z) := by
  let _ := flipInnerHom_preservesPullbacks Z
  exact (pp.isPushout.op.flip).map (innerHomFunctor.{u}.flip.obj Z)

private lemma transportedPullback {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    IsPullback
      ((innerHomFunctor.{u}.map pp.inl.op).app Z ≫ (tensorHomIso K B Z).hom)
      ((innerHomFunctor.{u}.map pp.inr.op).app Z ≫ (tensorHomIso L A Z).hom)
      ((ihom K).map (restriction s Z)) ((pre j).app (mapSpace A Z)) := by
  exact (mappedInnerPushout s j pp Z).of_iso
    (Iso.refl _) (tensorHomIso K B Z) (tensorHomIso L A Z) (tensorHomIso K A Z)
    (by simp) (by simp)
    (innerTensorHomIso_naturality_source K s Z)
    (innerTensorHomIso_naturality_scalar j A Z)

private def pointIso {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    mapSpace pp.pt Z ≅ (scalarSquare s j Z).pt :=
  (transportedPullback s j pp Z).isoIsPullback _ _ (scalarSquare s j Z).isPullback

private lemma pointIso_hom_fst {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (pointIso s j pp Z).hom ≫ (scalarSquare s j Z).fst =
      (innerHomFunctor.{u}.map pp.inl.op).app Z ≫ (tensorHomIso K B Z).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ (transportedPullback s j pp Z)
    (scalarSquare s j Z).isPullback

private lemma pointIso_hom_snd {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (pointIso s j pp Z).hom ≫ (scalarSquare s j Z).snd =
      (innerHomFunctor.{u}.map pp.inr.op).app Z ≫ (tensorHomIso L A Z).hom :=
  IsPullback.isoIsPullback_hom_snd _ _ (transportedPullback s j pp Z)
    (scalarSquare s j Z).isPullback

private lemma pointIso_inv_fst {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (pointIso s j pp Z).inv ≫ (innerHomFunctor.{u}.map pp.inl.op).app Z =
      (scalarSquare s j Z).fst ≫ (tensorHomIso K B Z).inv := by
  apply (Iso.eq_comp_inv (tensorHomIso K B Z)).2
  exact (Category.assoc _ _ _).trans
    (IsPullback.isoIsPullback_inv_fst _ _ (transportedPullback s j pp Z)
      (scalarSquare s j Z).isPullback)

private lemma pointIso_inv_snd {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (pointIso s j pp Z).inv ≫ (innerHomFunctor.{u}.map pp.inr.op).app Z =
      (scalarSquare s j Z).snd ≫ (tensorHomIso L A Z).inv := by
  apply (Iso.eq_comp_inv (tensorHomIso L A Z)).2
  exact (Category.assoc _ _ _).trans
    (IsPullback.isoIsPullback_inv_snd _ _ (transportedPullback s j pp Z)
      (scalarSquare s j Z).isPullback)

set_option backward.isDefEq.respectTransparency false in
private lemma original_square {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (tensorHomIso L B Z).hom ≫ (scalarSquare s j Z).π =
      (innerHomFunctor.{u}.map pp.ι.op).app Z ≫ (pointIso s j pp Z).hom := by
  apply (scalarSquare s j Z).hom_ext
  · have hinl :
        (innerHomFunctor.{u}.map pp.ι.op).app Z ≫
            (innerHomFunctor.{u}.map pp.inl.op).app Z =
          (innerHomFunctor.{u}.map ((innerTensorBifunctor.{u}.obj B).map j).op).app Z := by
      simpa only [op_comp, Functor.map_comp, NatTrans.comp_app] using
        congrArg (fun f => (innerHomFunctor.{u}.map f.op).app Z) pp.inl_ι
    calc
      ((tensorHomIso L B Z).hom ≫ (scalarSquare s j Z).π) ≫ (scalarSquare s j Z).fst =
          (tensorHomIso L B Z).hom ≫
            ((scalarSquare s j Z).π ≫ (scalarSquare s j Z).fst) := Category.assoc _ _ _
      _ = (tensorHomIso L B Z).hom ≫ (pre j).app (mapSpace B Z) :=
        congrArg (fun f => (tensorHomIso L B Z).hom ≫ f) (scalarSquare s j Z).π_fst
      _ = (innerHomFunctor.{u}.map ((innerTensorBifunctor.{u}.obj B).map j).op).app Z ≫
          (tensorHomIso K B Z).hom := (innerTensorHomIso_naturality_scalar j B Z).symm
      _ = ((innerHomFunctor.{u}.map pp.ι.op).app Z ≫
            (innerHomFunctor.{u}.map pp.inl.op).app Z) ≫ (tensorHomIso K B Z).hom :=
        congrArg (fun f => f ≫ (tensorHomIso K B Z).hom) hinl.symm
      _ = (innerHomFunctor.{u}.map pp.ι.op).app Z ≫
          ((innerHomFunctor.{u}.map pp.inl.op).app Z ≫ (tensorHomIso K B Z).hom) :=
        Category.assoc _ _ _
      _ = (innerHomFunctor.{u}.map pp.ι.op).app Z ≫
          ((pointIso s j pp Z).hom ≫ (scalarSquare s j Z).fst) :=
        congrArg (fun f => (innerHomFunctor.{u}.map pp.ι.op).app Z ≫ f)
          (pointIso_hom_fst s j pp Z).symm
      _ = ((innerHomFunctor.{u}.map pp.ι.op).app Z ≫ (pointIso s j pp Z).hom) ≫
          (scalarSquare s j Z).fst := (Category.assoc _ _ _).symm
  · have hinr :
        (innerHomFunctor.{u}.map pp.ι.op).app Z ≫
            (innerHomFunctor.{u}.map pp.inr.op).app Z =
          (innerHomFunctor.{u}.map ((innerTensorBifunctor.{u}.map s).app L).op).app Z := by
      simpa only [op_comp, Functor.map_comp, NatTrans.comp_app] using
        congrArg (fun f => (innerHomFunctor.{u}.map f.op).app Z) pp.inr_ι
    calc
      ((tensorHomIso L B Z).hom ≫ (scalarSquare s j Z).π) ≫ (scalarSquare s j Z).snd =
          (tensorHomIso L B Z).hom ≫
            ((scalarSquare s j Z).π ≫ (scalarSquare s j Z).snd) := Category.assoc _ _ _
      _ = (tensorHomIso L B Z).hom ≫ (ihom L).map (restriction s Z) :=
        congrArg (fun f => (tensorHomIso L B Z).hom ≫ f) (scalarSquare s j Z).π_snd
      _ = (innerHomFunctor.{u}.map ((innerTensorBifunctor.{u}.map s).app L).op).app Z ≫
          (tensorHomIso L A Z).hom := (innerTensorHomIso_naturality_source L s Z).symm
      _ = ((innerHomFunctor.{u}.map pp.ι.op).app Z ≫
            (innerHomFunctor.{u}.map pp.inr.op).app Z) ≫ (tensorHomIso L A Z).hom :=
        congrArg (fun f => f ≫ (tensorHomIso L A Z).hom) hinr.symm
      _ = (innerHomFunctor.{u}.map pp.ι.op).app Z ≫
          ((innerHomFunctor.{u}.map pp.inr.op).app Z ≫ (tensorHomIso L A Z).hom) :=
        Category.assoc _ _ _
      _ = (innerHomFunctor.{u}.map pp.ι.op).app Z ≫
          ((pointIso s j pp Z).hom ≫ (scalarSquare s j Z).snd) :=
        congrArg (fun f => (innerHomFunctor.{u}.map pp.ι.op).app Z ≫ f)
          (pointIso_hom_snd s j pp Z).symm
      _ = ((innerHomFunctor.{u}.map pp.ι.op).app Z ≫ (pointIso s j pp Z).hom) ≫
          (scalarSquare s j Z).snd := (Category.assoc _ _ _).symm

/-- The actual whole inner-Hom/Leibniz comparison for every supplied original pushout. -/
def innerLeibnizHomIso {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    Arrow.mk ((innerHomFunctor.{u}.map pp.ι.op).app Z) ≅
      Arrow.mk (SSet.ihomToPullback j ((innerHomFunctor.{u}.map s.op).app Z)) :=
  Arrow.isoMk (tensorHomIso L B Z) (pointIso s j pp Z) (original_square s j pp Z)

/-- The original whole-arrow source component is the established tensor-Hom map. -/
lemma innerLeibnizHomIso_hom_left {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (innerLeibnizHomIso s j pp Z).hom.left = (innerTensorHomIso L B).hom.app Z := rfl

/-- First original forward projection. -/
@[reassoc]
lemma innerLeibnizHomIso_hom_right_fst {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (innerLeibnizHomIso s j pp Z).hom.right ≫
        (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j
          ((innerHomFunctor.{u}.map s.op).app Z)).fst =
      (innerHomFunctor.{u}.map pp.inl.op).app Z ≫ (innerTensorHomIso K B).hom.app Z :=
  pointIso_hom_fst s j pp Z

/-- Second original forward projection. -/
@[reassoc]
lemma innerLeibnizHomIso_hom_right_snd {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (innerLeibnizHomIso s j pp Z).hom.right ≫
        (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j
          ((innerHomFunctor.{u}.map s.op).app Z)).snd =
      (innerHomFunctor.{u}.map pp.inr.op).app Z ≫ (innerTensorHomIso L A).hom.app Z :=
  pointIso_hom_snd s j pp Z

/-- First original inverse projection. -/
@[reassoc]
lemma innerLeibnizHomIso_inv_right_fst {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (innerLeibnizHomIso s j pp Z).inv.right ≫ (innerHomFunctor.{u}.map pp.inl.op).app Z =
      (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j
          ((innerHomFunctor.{u}.map s.op).app Z)).fst ≫ (innerTensorHomIso K B).inv.app Z :=
  pointIso_inv_fst s j pp Z

/-- Second original inverse projection. -/
@[reassoc]
lemma innerLeibnizHomIso_inv_right_snd {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (innerLeibnizHomIso s j pp Z).inv.right ≫ (innerHomFunctor.{u}.map pp.inr.op).app Z =
      (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j
          ((innerHomFunctor.{u}.map s.op).app Z)).snd ≫ (innerTensorHomIso L A).inv.app Z :=
  pointIso_inv_snd s j pp Z

private abbrev inputArrowMap {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) {Z Z' : SimplicialSpace.{u}} (z : Z ⟶ Z') :
    Arrow.mk ((innerHomFunctor.{u}.map pp.ι.op).app Z) ⟶
      Arrow.mk ((innerHomFunctor.{u}.map pp.ι.op).app Z') :=
  Arrow.homMk ((innerHomFunctor.{u}.obj (op ((innerTensor L).obj B))).map z)
    ((innerHomFunctor.{u}.obj (op pp.pt)).map z)
    ((innerHomFunctor.{u}.map pp.ι.op).naturality z)

private abbrev restrictionArrowMap {A B : SimplicialSpace.{u}} (s : A ⟶ B)
    {Z Z' : SimplicialSpace.{u}} (z : Z ⟶ Z') :
    Arrow.mk (restriction s Z) ⟶ Arrow.mk (restriction s Z') :=
  Arrow.homMk ((innerHomFunctor.{u}.obj (op B)).map z)
    ((innerHomFunctor.{u}.obj (op A)).map z)
    ((innerHomFunctor.{u}.map s.op).naturality z)

private abbrev scalarArrowMap {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) {Z Z' : SimplicialSpace.{u}} (z : Z ⟶ Z') :
    Arrow.mk (scalarSquare s j Z).π ⟶ Arrow.mk (scalarSquare s j Z').π :=
  Functor.PullbackObjObj.mapArrowRight
    (f₁ := Arrow.mk j) (f₃ := Arrow.mk (restriction s Z))
    (f₃' := Arrow.mk (restriction s Z')) (scalarSquare s j Z) (scalarSquare s j Z')
    (restrictionArrowMap s z)

private lemma scalar_map_fst {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) {Z Z' : SimplicialSpace.{u}} (z : Z ⟶ Z') :
    (scalarArrowMap s j z).right ≫ (scalarSquare s j Z').fst =
      (scalarSquare s j Z).fst ≫ (ihom K).map ((innerHomFunctor.{u}.obj (op B)).map z) := by
  change (scalarSquare s j Z').isPullback.lift _ _ _ ≫ (scalarSquare s j Z').fst = _
  exact (scalarSquare s j Z').isPullback.lift_fst _ _ _

private lemma scalar_map_snd {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) {Z Z' : SimplicialSpace.{u}} (z : Z ⟶ Z') :
    (scalarArrowMap s j z).right ≫ (scalarSquare s j Z').snd =
      (scalarSquare s j Z).snd ≫ (ihom L).map ((innerHomFunctor.{u}.obj (op A)).map z) := by
  change (scalarSquare s j Z').isPullback.lift _ _ _ ≫ (scalarSquare s j Z').snd = _
  exact (scalarSquare s j Z').isPullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Naturality is the full original Z-square equation, on both components. -/
lemma innerLeibnizHomIso_naturality {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) {Z Z' : SimplicialSpace.{u}} (z : Z ⟶ Z') :
    Arrow.homMk ((innerHomFunctor.{u}.obj (op ((innerTensor L).obj B))).map z)
        ((innerHomFunctor.{u}.obj (op pp.pt)).map z)
        ((innerHomFunctor.{u}.map pp.ι.op).naturality z) ≫
      (innerLeibnizHomIso s j pp Z').hom =
    (innerLeibnizHomIso s j pp Z).hom ≫
      Functor.PullbackObjObj.mapArrowRight
        (f₁ := Arrow.mk j)
        (f₃ := Arrow.mk ((innerHomFunctor.{u}.map s.op).app Z))
        (f₃' := Arrow.mk ((innerHomFunctor.{u}.map s.op).app Z'))
        (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j
          ((innerHomFunctor.{u}.map s.op).app Z))
        (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j
          ((innerHomFunctor.{u}.map s.op).app Z'))
        (Arrow.homMk ((innerHomFunctor.{u}.obj (op B)).map z)
          ((innerHomFunctor.{u}.obj (op A)).map z)
          ((innerHomFunctor.{u}.map s.op).naturality z)) := by
  change inputArrowMap s j pp z ≫ (innerLeibnizHomIso s j pp Z').hom =
    (innerLeibnizHomIso s j pp Z).hom ≫ scalarArrowMap s j z
  apply Arrow.hom_ext
  · change (innerHomFunctor.{u}.obj (op ((innerTensor L).obj B))).map z ≫
        (tensorHomIso L B Z').hom =
      (tensorHomIso L B Z).hom ≫ (ihom L).map ((innerHomFunctor.{u}.obj (op B)).map z)
    exact (innerTensorHomIso L B).hom.naturality z
  · change (innerHomFunctor.{u}.obj (op pp.pt)).map z ≫ (pointIso s j pp Z').hom =
      (pointIso s j pp Z).hom ≫ (scalarArrowMap s j z).right
    apply (scalarSquare s j Z').hom_ext
    · calc
        ((innerHomFunctor.{u}.obj (op pp.pt)).map z ≫ (pointIso s j pp Z').hom) ≫
            (scalarSquare s j Z').fst =
          (innerHomFunctor.{u}.obj (op pp.pt)).map z ≫
            ((pointIso s j pp Z').hom ≫ (scalarSquare s j Z').fst) :=
          Category.assoc _ _ _
        _ = (innerHomFunctor.{u}.obj (op pp.pt)).map z ≫
            ((innerHomFunctor.{u}.map pp.inl.op).app Z' ≫ (tensorHomIso K B Z').hom) :=
          congrArg (fun f => (innerHomFunctor.{u}.obj (op pp.pt)).map z ≫ f)
            (pointIso_hom_fst s j pp Z')
        _ = ((innerHomFunctor.{u}.obj (op pp.pt)).map z ≫
            (innerHomFunctor.{u}.map pp.inl.op).app Z') ≫ (tensorHomIso K B Z').hom :=
          (Category.assoc _ _ _).symm
        _ = ((innerHomFunctor.{u}.map pp.inl.op).app Z ≫
            (innerHomFunctor.{u}.obj (op ((innerTensor K).obj B))).map z) ≫
              (tensorHomIso K B Z').hom :=
          congrArg (fun f => f ≫ (tensorHomIso K B Z').hom)
            ((innerHomFunctor.{u}.map pp.inl.op).naturality z)
        _ = (innerHomFunctor.{u}.map pp.inl.op).app Z ≫
            ((innerHomFunctor.{u}.obj (op ((innerTensor K).obj B))).map z ≫
              (tensorHomIso K B Z').hom) := Category.assoc _ _ _
        _ = (innerHomFunctor.{u}.map pp.inl.op).app Z ≫
            ((tensorHomIso K B Z).hom ≫
              (ihom K).map ((innerHomFunctor.{u}.obj (op B)).map z)) :=
          congrArg (fun f => (innerHomFunctor.{u}.map pp.inl.op).app Z ≫ f)
            ((innerTensorHomIso K B).hom.naturality z)
        _ = ((innerHomFunctor.{u}.map pp.inl.op).app Z ≫ (tensorHomIso K B Z).hom) ≫
            (ihom K).map ((innerHomFunctor.{u}.obj (op B)).map z) :=
          (Category.assoc _ _ _).symm
        _ = ((pointIso s j pp Z).hom ≫ (scalarSquare s j Z).fst) ≫
            (ihom K).map ((innerHomFunctor.{u}.obj (op B)).map z) :=
          congrArg (fun f => f ≫ (ihom K).map ((innerHomFunctor.{u}.obj (op B)).map z))
            (pointIso_hom_fst s j pp Z).symm
        _ = (pointIso s j pp Z).hom ≫ ((scalarSquare s j Z).fst ≫
            (ihom K).map ((innerHomFunctor.{u}.obj (op B)).map z)) := Category.assoc _ _ _
        _ = (pointIso s j pp Z).hom ≫
            ((scalarArrowMap s j z).right ≫ (scalarSquare s j Z').fst) :=
          congrArg (fun f => (pointIso s j pp Z).hom ≫ f) (scalar_map_fst s j z).symm
        _ = ((pointIso s j pp Z).hom ≫ (scalarArrowMap s j z).right) ≫
            (scalarSquare s j Z').fst := (Category.assoc _ _ _).symm

    · calc
        ((innerHomFunctor.{u}.obj (op pp.pt)).map z ≫ (pointIso s j pp Z').hom) ≫
            (scalarSquare s j Z').snd =
          (innerHomFunctor.{u}.obj (op pp.pt)).map z ≫
            ((pointIso s j pp Z').hom ≫ (scalarSquare s j Z').snd) :=
          Category.assoc _ _ _
        _ = (innerHomFunctor.{u}.obj (op pp.pt)).map z ≫
            ((innerHomFunctor.{u}.map pp.inr.op).app Z' ≫ (tensorHomIso L A Z').hom) :=
          congrArg (fun f => (innerHomFunctor.{u}.obj (op pp.pt)).map z ≫ f)
            (pointIso_hom_snd s j pp Z')
        _ = ((innerHomFunctor.{u}.obj (op pp.pt)).map z ≫
            (innerHomFunctor.{u}.map pp.inr.op).app Z') ≫ (tensorHomIso L A Z').hom :=
          (Category.assoc _ _ _).symm
        _ = ((innerHomFunctor.{u}.map pp.inr.op).app Z ≫
            (innerHomFunctor.{u}.obj (op ((innerTensor L).obj A))).map z) ≫
              (tensorHomIso L A Z').hom :=
          congrArg (fun f => f ≫ (tensorHomIso L A Z').hom)
            ((innerHomFunctor.{u}.map pp.inr.op).naturality z)
        _ = (innerHomFunctor.{u}.map pp.inr.op).app Z ≫
            ((innerHomFunctor.{u}.obj (op ((innerTensor L).obj A))).map z ≫
              (tensorHomIso L A Z').hom) := Category.assoc _ _ _
        _ = (innerHomFunctor.{u}.map pp.inr.op).app Z ≫
            ((tensorHomIso L A Z).hom ≫
              (ihom L).map ((innerHomFunctor.{u}.obj (op A)).map z)) :=
          congrArg (fun f => (innerHomFunctor.{u}.map pp.inr.op).app Z ≫ f)
            ((innerTensorHomIso L A).hom.naturality z)
        _ = ((innerHomFunctor.{u}.map pp.inr.op).app Z ≫ (tensorHomIso L A Z).hom) ≫
            (ihom L).map ((innerHomFunctor.{u}.obj (op A)).map z) :=
          (Category.assoc _ _ _).symm
        _ = ((pointIso s j pp Z).hom ≫ (scalarSquare s j Z).snd) ≫
            (ihom L).map ((innerHomFunctor.{u}.obj (op A)).map z) :=
          congrArg (fun f => f ≫ (ihom L).map ((innerHomFunctor.{u}.obj (op A)).map z))
            (pointIso_hom_snd s j pp Z).symm
        _ = (pointIso s j pp Z).hom ≫ ((scalarSquare s j Z).snd ≫
            (ihom L).map ((innerHomFunctor.{u}.obj (op A)).map z)) := Category.assoc _ _ _
        _ = (pointIso s j pp Z).hom ≫
            ((scalarArrowMap s j z).right ≫ (scalarSquare s j Z').snd) :=
          congrArg (fun f => (pointIso s j pp Z).hom ≫ f) (scalar_map_snd s j z).symm
        _ = ((pointIso s j pp Z).hom ≫ (scalarArrowMap s j z).right) ≫
            (scalarSquare s j Z').snd := (Category.assoc _ _ _).symm

/-- Both directions are inverses as maps of the actual original arrows. -/
lemma innerLeibnizHomIso_inverse_equations {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.{u}.PushoutObjObj s j) (Z : SimplicialSpace.{u}) :
    (innerLeibnizHomIso s j pp Z).hom ≫ (innerLeibnizHomIso s j pp Z).inv = 𝟙 _ ∧
      (innerLeibnizHomIso s j pp Z).inv ≫ (innerLeibnizHomIso s j pp Z).hom = 𝟙 _ :=
  ⟨(innerLeibnizHomIso s j pp Z).hom_inv_id, (innerLeibnizHomIso s j pp Z).inv_hom_id⟩

end SimplicialSpace
