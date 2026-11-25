/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageComposition

/-! # Coherence of the actual small étale sheaf functors

All comparisons below are the concrete base-change comparisons and their
adjunction mates. A common composite is named explicitly when a category
identity or associativity equality changes its expression.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

set_option backward.isDefEq.respectTransparency.types false in
/-- The same canonical base-change comparison with an explicitly named composite. -/
def smallEtaleBaseChangeCompTo {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    smallEtaleBaseChange fg ≅ smallEtaleBaseChange g ⋙ smallEtaleBaseChange f :=
  MorphismProperty.Over.pullbackComp
    (P := @AlgebraicGeometry.Etale.{u}) (Q := ⊤) f g fg hfg

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual identity comparison is the original pullback projection. -/
theorem smallEtaleBaseChangeId_hom_app_left (X : Scheme.{u}) (U : X.Etale) :
    ((smallEtaleBaseChangeId X).hom.app U).left = pullback.fst U.hom (𝟙 X) := by
  let G := Scheme.Etale.forget X
  let H := (Functor.whiskeringRight X.Etale X.Etale (CategoryTheory.Over X)).obj G
  let e := MorphismProperty.Over.pullbackCompForgetIso
      (P := @AlgebraicGeometry.Etale.{u}) (Q := ⊤) (𝟙 X) ≪≫
    Functor.isoWhiskerLeft G (CategoryTheory.Over.pullbackId (X := X)) ≪≫
    Functor.rightUnitor G ≪≫ (Functor.leftUnitor G).symm
  have hh : H.map (smallEtaleBaseChangeId X).hom = e.hom := H.map_preimage e.hom
  have h := congrArg (fun τ => (τ.app U).left) hh
  simpa [e, H, G, Scheme.Etale.forget, MorphismProperty.Over.forget,
    MorphismProperty.Comma.forget, CategoryTheory.Over.pullbackId, conjugateIsoEquiv,
    conjugateEquiv_adjunction_id] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse of the right identity base-change comparison is the
same actual identity comparison followed by base change. -/
theorem smallEtaleBaseChange_comp_id {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleBaseChangeCompTo f (𝟙 Y) f (Category.comp_id f).symm).symm =
      Functor.isoWhiskerRight (smallEtaleBaseChangeId Y) (smallEtaleBaseChange f) ≪≫
        Functor.leftUnitor (smallEtaleBaseChange f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp [smallEtaleBaseChangeCompTo, MorphismProperty.Over.pullbackComp,
      NatIso.ofComponents, MorphismProperty.Over.isoMk,
      MorphismProperty.Over.pullback_map_left, smallEtaleBaseChangeId_hom_app_left,
      Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse of the left identity base-change comparison is the
same actual identity comparison on the resulting original étale object. -/
theorem smallEtaleBaseChange_id_comp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleBaseChangeCompTo (𝟙 X) f f (Category.id_comp f).symm).symm =
      Functor.isoWhiskerLeft (smallEtaleBaseChange f) (smallEtaleBaseChangeId X) ≪≫
        Functor.rightUnitor (smallEtaleBaseChange f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp [smallEtaleBaseChangeCompTo, MorphismProperty.Over.pullbackComp,
      NatIso.ofComponents, MorphismProperty.Over.isoMk,
      smallEtaleBaseChangeId_hom_app_left, Category.assoc, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The two canonical comparisons of the original triple fiber product agree. -/
theorem smallEtaleBaseChange_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    smallEtaleBaseChangeCompTo f (g ≫ h) (f ≫ g ≫ h) rfl ≪≫
        Functor.isoWhiskerRight (smallEtaleBaseChangeComp g h) (smallEtaleBaseChange f) ≪≫
        Functor.associator (smallEtaleBaseChange h) (smallEtaleBaseChange g)
          (smallEtaleBaseChange f) =
      smallEtaleBaseChangeCompTo (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h).symm ≪≫
        Functor.isoWhiskerLeft (smallEtaleBaseChange h) (smallEtaleBaseChangeComp f g) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext U
  apply MorphismProperty.Over.Hom.ext
  change
    ((smallEtaleBaseChange f).map ((smallEtaleBaseChangeComp g h).inv.app U)).left ≫
        ((smallEtaleBaseChangeCompTo f (g ≫ h) (f ≫ g ≫ h) rfl).inv.app U).left =
      ((smallEtaleBaseChangeComp f g).inv.app ((smallEtaleBaseChange h).obj U)).left ≫
        ((smallEtaleBaseChangeCompTo (f ≫ g) h (f ≫ g ≫ h)
          (Category.assoc f g h).symm).inv.app U).left
  apply pullback.hom_ext <;>
    simp [smallEtaleBaseChangeCompTo, smallEtaleBaseChangeComp,
      MorphismProperty.Over.pullbackComp, NatIso.ofComponents, MorphismProperty.Over.isoMk,
      MorphismProperty.Over.pullback_map_left, Category.assoc]


/-- Equality of original morphisms transports the same literal direct-image functor. -/
def smallEtaleDirectImageCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    smallEtaleDirectImage.{u, max u w} f ≅ smallEtaleDirectImage.{u, max u w} g :=
  eqToIso (congrArg (fun a => smallEtaleDirectImage.{u, max u w} a) h)

/-- Equality of original morphisms transports the same constructed inverse image. -/
def smallEtaleInverseImageCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    smallEtaleInverseImage.{u, w} f ≅ smallEtaleInverseImage.{u, w} g :=
  eqToIso (congrArg (fun a => smallEtaleInverseImage.{u, w} a) h)

/-- The same actual direct-image comparison with an explicitly named composite. -/
def smallEtaleDirectImageCompTo {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    smallEtaleDirectImage.{u, max u w} f ⋙ smallEtaleDirectImage.{u, max u w} g ≅
      smallEtaleDirectImage.{u, max u w} fg := by
  let : (smallEtaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous f
  let : (smallEtaleBaseChange g).IsContinuous Z.smallEtaleTopology Y.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous g
  let : (smallEtaleBaseChange fg).IsContinuous Z.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous fg
  exact Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeCompTo f g fg hfg).symm
    AddCommGrpCat.{max u w} Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- The same actual inverse-image comparison with an explicitly named composite. -/
def smallEtaleInverseImageCompTo {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    smallEtaleInverseImage.{u, w} g ⋙ smallEtaleInverseImage.{u, w} f ≅
      smallEtaleInverseImage.{u, w} fg :=
  Adjunction.leftAdjointCompIso (smallEtaleInverseImageAdjunction.{u, w} g)
    (smallEtaleInverseImageAdjunction.{u, w} f)
    (smallEtaleInverseImageAdjunction.{u, w} fg)
    (smallEtaleDirectImageCompTo.{u, w} f g fg hfg)

/-- Naming a composite changes the preceding actual comparison only by equality transport. -/
theorem smallEtaleDirectImageCompTo_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    smallEtaleDirectImageCompTo.{u, w} f g fg hfg =
      smallEtaleDirectImageCompIso.{u, w} f g ≪≫ smallEtaleDirectImageCongr.{u, w} hfg.symm := by
  subst fg
  simp only [smallEtaleDirectImageCongr, eqToIso_refl, Iso.trans_refl]
  rfl

/-- Naming a composite changes the preceding actual mate only by equality transport. -/
theorem smallEtaleInverseImageCompTo_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    smallEtaleInverseImageCompTo.{u, w} f g fg hfg =
      smallEtaleInverseImageCompIso.{u, w} f g ≪≫ smallEtaleInverseImageCongr.{u, w} hfg.symm := by
  subst fg
  simp only [smallEtaleInverseImageCongr, eqToIso_refl, Iso.trans_refl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The composition comparison has the literal restriction-map component. -/
theorem smallEtaleDirectImageCompTo_hom_app_hom_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (U : Z.Etaleᵒᵖ) :
    ((smallEtaleDirectImageCompTo.{u, w} f g fg hfg).hom.app Q).hom.app U =
      Q.obj.map ((smallEtaleBaseChangeCompTo f g fg hfg).hom.app U.unop).op := by
  dsimp [smallEtaleDirectImageCompTo, smallEtaleDirectImage,
    Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The identity comparison has the literal restriction-map component. -/
theorem smallEtaleDirectImageIdIso_hom_app_hom_app (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (U : X.Etaleᵒᵖ) :
    ((smallEtaleDirectImageIdIso.{u, w} X).hom.app Q).hom.app U =
      Q.obj.map ((smallEtaleBaseChangeId X).inv.app U.unop).op := by
  dsimp [smallEtaleDirectImageIdIso, Functor.sheafPushforwardContinuousId',
    Functor.sheafPushforwardContinuousId, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual direct-image comparison satisfies right identity coherence. -/
theorem smallEtaleDirectImage_comp_id {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleDirectImageCompTo.{u, w} f (𝟙 Y) f (Category.comp_id f).symm =
      Functor.isoWhiskerLeft (smallEtaleDirectImage.{u, max u w} f)
          (smallEtaleDirectImageIdIso.{u, w} Y) ≪≫
        Functor.rightUnitor (smallEtaleDirectImage.{u, max u w} f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  apply (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}).map_injective
  apply NatTrans.ext
  funext U
  have h := congrArg (fun e => Q.obj.map ((e.inv.app U.unop).op))
    (smallEtaleBaseChange_comp_id f)
  simpa [smallEtaleDirectImageCompTo_hom_app_hom_app,
    smallEtaleDirectImageIdIso_hom_app_hom_app,
    smallEtaleDirectImage_obj_map] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual direct-image comparison satisfies left identity coherence. -/
theorem smallEtaleDirectImage_id_comp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleDirectImageCompTo.{u, w} (𝟙 X) f f (Category.id_comp f).symm =
      Functor.isoWhiskerRight (smallEtaleDirectImageIdIso.{u, w} X)
          (smallEtaleDirectImage.{u, max u w} f) ≪≫
        Functor.leftUnitor (smallEtaleDirectImage.{u, max u w} f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  apply (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}).map_injective
  apply NatTrans.ext
  funext U
  have h := congrArg (fun e => Q.obj.map ((e.inv.app U.unop).op))
    (smallEtaleBaseChange_id_comp f)
  simpa [smallEtaleDirectImageCompTo_hom_app_hom_app,
    smallEtaleDirectImageIdIso_hom_app_hom_app,
    smallEtaleDirectImage, Functor.sheafPushforwardContinuous] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The two actual direct-image comparisons of a triple composite agree. -/
theorem smallEtaleDirectImage_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (smallEtaleDirectImage.{u, max u w} f)
        (smallEtaleDirectImageCompTo.{u, w} g h (g ≫ h) rfl) ≪≫
        smallEtaleDirectImageCompTo.{u, w} f (g ≫ h) (f ≫ g ≫ h) rfl =
      (Functor.associator (smallEtaleDirectImage.{u, max u w} f)
          (smallEtaleDirectImage.{u, max u w} g)
          (smallEtaleDirectImage.{u, max u w} h)).symm ≪≫
        Functor.isoWhiskerRight (smallEtaleDirectImageCompTo.{u, w} f g (f ≫ g) rfl)
          (smallEtaleDirectImage.{u, max u w} h) ≪≫
        smallEtaleDirectImageCompTo.{u, w} (f ≫ g) h (f ≫ g ≫ h)
          (Category.assoc f g h).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  apply (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{max u w}).map_injective
  apply NatTrans.ext
  funext U
  have hh := congrArg (fun e => Q.obj.map ((e.hom.app U.unop).op))
    (smallEtaleBaseChange_assoc f g h)
  simpa [smallEtaleDirectImageCompTo_hom_app_hom_app,
    smallEtaleDirectImage, Functor.sheafPushforwardContinuous, Functor.map_comp,
    smallEtaleBaseChangeCompTo, smallEtaleBaseChangeComp] using hh

/-- The actual inverse-image comparison satisfies right-morphism identity coherence. -/
theorem smallEtaleInverseImage_comp_id {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleInverseImageCompTo.{u, w} f (𝟙 Y) f (Category.comp_id f).symm =
      Functor.isoWhiskerRight (smallEtaleInverseImageIdIso.{u, w} Y)
          (smallEtaleInverseImage.{u, w} f) ≪≫
        Functor.leftUnitor (smallEtaleInverseImage.{u, w} f) := by
  exact Adjunction.leftAdjointCompIso_id_comp
    (smallEtaleInverseImageAdjunction.{u, w} (𝟙 Y))
    (smallEtaleInverseImageAdjunction.{u, w} f)
    (smallEtaleDirectImageCompTo.{u, w} f (𝟙 Y) f (Category.comp_id f).symm)
    (smallEtaleDirectImageIdIso.{u, w} Y) (smallEtaleDirectImage_comp_id.{u, w} f)

/-- The actual inverse-image comparison satisfies left-morphism identity coherence. -/
theorem smallEtaleInverseImage_id_comp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleInverseImageCompTo.{u, w} (𝟙 X) f f (Category.id_comp f).symm =
      Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} f)
          (smallEtaleInverseImageIdIso.{u, w} X) ≪≫
        Functor.rightUnitor (smallEtaleInverseImage.{u, w} f) := by
  exact Adjunction.leftAdjointCompIso_comp_id
    (smallEtaleInverseImageAdjunction.{u, w} f)
    (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X))
    (smallEtaleDirectImageCompTo.{u, w} (𝟙 X) f f (Category.id_comp f).symm)
    (smallEtaleDirectImageIdIso.{u, w} X) (smallEtaleDirectImage_id_comp.{u, w} f)

/-- Inverse-image associativity follows from the proved actual direct-image
associativity and the same six concrete adjunctions. -/
theorem smallEtaleInverseImage_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} h)
        (smallEtaleInverseImageCompTo.{u, w} f g (f ≫ g) rfl) ≪≫
        smallEtaleInverseImageCompTo.{u, w} (f ≫ g) h (f ≫ g ≫ h)
          (Category.assoc f g h).symm =
      (Functor.associator (smallEtaleInverseImage.{u, w} h)
          (smallEtaleInverseImage.{u, w} g) (smallEtaleInverseImage.{u, w} f)).symm ≪≫
        Functor.isoWhiskerRight (smallEtaleInverseImageCompTo.{u, w} g h (g ≫ h) rfl)
          (smallEtaleInverseImage.{u, w} f) ≪≫
        smallEtaleInverseImageCompTo.{u, w} f (g ≫ h) (f ≫ g ≫ h) rfl := by
  exact Adjunction.leftAdjointCompIso_assoc
    (smallEtaleInverseImageAdjunction.{u, w} h)
    (smallEtaleInverseImageAdjunction.{u, w} g)
    (smallEtaleInverseImageAdjunction.{u, w} f)
    (smallEtaleInverseImageAdjunction.{u, w} (g ≫ h))
    (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g))
    (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g ≫ h))
    (smallEtaleDirectImageCompTo.{u, w} g h (g ≫ h) rfl)
    (smallEtaleDirectImageCompTo.{u, w} f g (f ≫ g) rfl)
    (smallEtaleDirectImageCompTo.{u, w} (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h).symm)
    (smallEtaleDirectImageCompTo.{u, w} f (g ≫ h) (f ≫ g ≫ h) rfl)
    (smallEtaleDirectImage_assoc.{u, w} f g h)

/-- The identity comparison commutes with the actual adjunction unit. -/
theorem smallEtaleInverseImageIdIso_unit (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleDirectImageIdIso.{u, w} X).inv.app Q =
      (smallEtaleInverseImageUnit.{u, w} (𝟙 X)).app Q ≫
        (smallEtaleDirectImage.{u, max u w} (𝟙 X)).map
          ((smallEtaleInverseImageIdIso.{u, w} X).hom.app Q) := by
  simpa only [smallEtaleInverseImageIdIso_mate, smallEtaleInverseImageUnit,
    Adjunction.id_unit, Functor.id_obj, NatTrans.id_app, Category.id_comp] using
    (unit_conjugateEquiv
      (Adjunction.id (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
      (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X))
      (smallEtaleInverseImageIdIso.{u, w} X).hom Q)

/-- The identity comparison commutes with the actual adjunction counit. -/
theorem smallEtaleInverseImageIdIso_counit (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleInverseImage.{u, w} (𝟙 X)).map
        ((smallEtaleDirectImageIdIso.{u, w} X).inv.app R) ≫
        (smallEtaleInverseImageCounit.{u, w} (𝟙 X)).app R =
      (smallEtaleInverseImageIdIso.{u, w} X).hom.app R := by
  simpa only [smallEtaleInverseImageIdIso_mate, smallEtaleInverseImageCounit,
    Adjunction.id_counit, Functor.id_obj, Functor.comp_obj, NatTrans.id_app,
    Category.comp_id] using
    (conjugateEquiv_counit
      (Adjunction.id (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
      (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X))
      (smallEtaleInverseImageIdIso.{u, w} X).hom R)

/-- The composition comparison commutes with the same actual adjunction units. -/
theorem smallEtaleInverseImageCompIso_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (Q : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max u w}) :
    ((smallEtaleInverseImageAdjunction.{u, w} g).comp
        (smallEtaleInverseImageAdjunction.{u, w} f)).unit.app Q ≫
        (smallEtaleDirectImageCompIso.{u, w} f g).hom.app
          ((smallEtaleInverseImage.{u, w} g ⋙ smallEtaleInverseImage.{u, w} f).obj Q) =
      (smallEtaleInverseImageUnit.{u, w} (f ≫ g)).app Q ≫
        (smallEtaleDirectImage.{u, max u w} (f ≫ g)).map
          ((smallEtaleInverseImageCompIso.{u, w} f g).inv.app Q) := by
  simpa only [smallEtaleInverseImageCompIso_mate, smallEtaleInverseImageUnit] using
    (unit_conjugateEquiv
      ((smallEtaleInverseImageAdjunction.{u, w} g).comp
        (smallEtaleInverseImageAdjunction.{u, w} f))
      (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g))
      (smallEtaleInverseImageCompIso.{u, w} f g).inv Q)

/-- The composition comparison commutes with the same actual adjunction counits. -/
theorem smallEtaleInverseImageCompIso_counit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleInverseImage.{u, w} (f ≫ g)).map
        ((smallEtaleDirectImageCompIso.{u, w} f g).hom.app R) ≫
        (smallEtaleInverseImageCounit.{u, w} (f ≫ g)).app R =
      (smallEtaleInverseImageCompIso.{u, w} f g).inv.app
          ((smallEtaleDirectImage.{u, max u w} f ⋙ smallEtaleDirectImage.{u, max u w} g).obj R) ≫
        ((smallEtaleInverseImageAdjunction.{u, w} g).comp
          (smallEtaleInverseImageAdjunction.{u, w} f)).counit.app R := by
  simpa only [smallEtaleInverseImageCompIso_mate, smallEtaleInverseImageCounit] using
    (conjugateEquiv_counit
      ((smallEtaleInverseImageAdjunction.{u, w} g).comp
        (smallEtaleInverseImageAdjunction.{u, w} f))
      (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g))
      (smallEtaleInverseImageCompIso.{u, w} f g).inv R)

/-- The literal identity data, naturality, and unit/counit equations of the
same actual sheaf functors. This is an output property, with no supplied data. -/
def SmallEtaleIdentityCoherence (X : Scheme.{u}) : Prop :=
  let D := smallEtaleDirectImage.{u, max u w} (𝟙 X)
  let L := smallEtaleInverseImage.{u, w} (𝟙 X)
  let eD := smallEtaleDirectImageIdIso.{u, w} X
  let eL := smallEtaleInverseImageIdIso.{u, w} X
  Nonempty (D ≅ 𝟭 _) ∧ Nonempty (L ≅ 𝟭 _) ∧
  (∀ (Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q'),
    D.map τ ≫ eD.hom.app Q' = eD.hom.app Q ≫ τ) ∧
  (∀ (Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q'),
    L.map τ ≫ eL.hom.app Q' = eL.hom.app Q ≫ τ) ∧
  (conjugateEquiv (Adjunction.id (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
    (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X)) eL.hom = eD.inv) ∧
  (∀ Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w},
    eD.inv.app Q = (smallEtaleInverseImageUnit.{u, w} (𝟙 X)).app Q ≫
      D.map (eL.hom.app Q)) ∧
  ∀ R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w},
    L.map (eD.inv.app R) ≫ (smallEtaleInverseImageCounit.{u, w} (𝟙 X)).app R = eL.hom.app R

/-- The literal pair data, naturality, equality transport, and unit/counit
equations of the same actual sheaf functors and concrete adjunctions. -/
def SmallEtalePairCoherence {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  let Df := smallEtaleDirectImage.{u, max u w} f
  let Dg := smallEtaleDirectImage.{u, max u w} g
  let Dfg := smallEtaleDirectImage.{u, max u w} (f ≫ g)
  let Lf := smallEtaleInverseImage.{u, w} f
  let Lg := smallEtaleInverseImage.{u, w} g
  let Lfg := smallEtaleInverseImage.{u, w} (f ≫ g)
  let eD := smallEtaleDirectImageCompIso.{u, w} f g
  let eL := smallEtaleInverseImageCompIso.{u, w} f g
  Nonempty (Df ⋙ Dg ≅ Dfg) ∧ Nonempty (Lg ⋙ Lf ≅ Lfg) ∧
  (∀ (Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q'),
    (Df ⋙ Dg).map τ ≫ eD.hom.app Q' = eD.hom.app Q ≫ Dfg.map τ) ∧
  (∀ (Q Q' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q'),
    (Lg ⋙ Lf).map τ ≫ eL.hom.app Q' = eL.hom.app Q ≫ Lfg.map τ) ∧
  (conjugateEquiv ((smallEtaleInverseImageAdjunction.{u, w} g).comp
    (smallEtaleInverseImageAdjunction.{u, w} f))
    (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g)) eL.inv = eD.hom) ∧
  (∀ Q : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max u w},
    ((smallEtaleInverseImageAdjunction.{u, w} g).comp
      (smallEtaleInverseImageAdjunction.{u, w} f)).unit.app Q ≫ eD.hom.app ((Lg ⋙ Lf).obj Q) =
      (smallEtaleInverseImageUnit.{u, w} (f ≫ g)).app Q ≫ Dfg.map (eL.inv.app Q)) ∧
  (∀ R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w},
    Lfg.map (eD.hom.app R) ≫ (smallEtaleInverseImageCounit.{u, w} (f ≫ g)).app R =
      eL.inv.app ((Df ⋙ Dg).obj R) ≫
        ((smallEtaleInverseImageAdjunction.{u, w} g).comp
          (smallEtaleInverseImageAdjunction.{u, w} f)).counit.app R) ∧
  ∀ (fg : X ⟶ Z) (hfg : fg = f ≫ g),
    smallEtaleDirectImageCompTo.{u, w} f g fg hfg =
      eD ≪≫ smallEtaleDirectImageCongr.{u, w} hfg.symm ∧
    smallEtaleInverseImageCompTo.{u, w} f g fg hfg =
      eL ≪≫ smallEtaleInverseImageCongr.{u, w} hfg.symm

/-- Both identity coherence laws hold for both actual sheaf functors. -/
def SmallEtaleUnitCoherence {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (smallEtaleDirectImageCompTo.{u, w} f (𝟙 Y) f (Category.comp_id f).symm =
    Functor.isoWhiskerLeft (smallEtaleDirectImage.{u, max u w} f)
      (smallEtaleDirectImageIdIso.{u, w} Y) ≪≫
      Functor.rightUnitor (smallEtaleDirectImage.{u, max u w} f)) ∧
  (smallEtaleDirectImageCompTo.{u, w} (𝟙 X) f f (Category.id_comp f).symm =
    Functor.isoWhiskerRight (smallEtaleDirectImageIdIso.{u, w} X)
      (smallEtaleDirectImage.{u, max u w} f) ≪≫
      Functor.leftUnitor (smallEtaleDirectImage.{u, max u w} f)) ∧
  (smallEtaleInverseImageCompTo.{u, w} f (𝟙 Y) f (Category.comp_id f).symm =
    Functor.isoWhiskerRight (smallEtaleInverseImageIdIso.{u, w} Y)
      (smallEtaleInverseImage.{u, w} f) ≪≫
      Functor.leftUnitor (smallEtaleInverseImage.{u, w} f)) ∧
  (smallEtaleInverseImageCompTo.{u, w} (𝟙 X) f f (Category.id_comp f).symm =
    Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} f)
      (smallEtaleInverseImageIdIso.{u, w} X) ≪≫
      Functor.rightUnitor (smallEtaleInverseImage.{u, w} f))

/-- Both literal associativity diagrams commute for every original triple. -/
def SmallEtaleAssociativityCoherence {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) : Prop :=
  (Functor.isoWhiskerLeft (smallEtaleDirectImage.{u, max u w} f)
      (smallEtaleDirectImageCompTo.{u, w} g h (g ≫ h) rfl) ≪≫
      smallEtaleDirectImageCompTo.{u, w} f (g ≫ h) (f ≫ g ≫ h) rfl =
    (Functor.associator (smallEtaleDirectImage.{u, max u w} f)
      (smallEtaleDirectImage.{u, max u w} g)
      (smallEtaleDirectImage.{u, max u w} h)).symm ≪≫
      Functor.isoWhiskerRight (smallEtaleDirectImageCompTo.{u, w} f g (f ≫ g) rfl)
        (smallEtaleDirectImage.{u, max u w} h) ≪≫
      smallEtaleDirectImageCompTo.{u, w} (f ≫ g) h (f ≫ g ≫ h)
        (Category.assoc f g h).symm) ∧
  (Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} h)
      (smallEtaleInverseImageCompTo.{u, w} f g (f ≫ g) rfl) ≪≫
      smallEtaleInverseImageCompTo.{u, w} (f ≫ g) h (f ≫ g ≫ h)
        (Category.assoc f g h).symm =
    (Functor.associator (smallEtaleInverseImage.{u, w} h)
      (smallEtaleInverseImage.{u, w} g) (smallEtaleInverseImage.{u, w} f)).symm ≪≫
      Functor.isoWhiskerRight (smallEtaleInverseImageCompTo.{u, w} g h (g ≫ h) rfl)
        (smallEtaleInverseImage.{u, w} f) ≪≫
      smallEtaleInverseImageCompTo.{u, w} f (g ≫ h) (f ≫ g ≫ h) rfl)

/-- One globally fixed actual functor family has the full original identity,
composition, naturality, unit/counit, and identity/associativity coherence data,
for every original scheme and morphism and the independent coefficient universe. -/
theorem original_small_etale_sheaf_functor_coherence :
    (∀ X : Scheme.{u}, SmallEtaleIdentityCoherence.{u, w} X) ∧
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), SmallEtalePairCoherence.{u, w} f g) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y), SmallEtaleUnitCoherence.{u, w} f) ∧
    ∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
      SmallEtaleAssociativityCoherence.{u, w} f g h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X
    dsimp only [SmallEtaleIdentityCoherence]
    exact ⟨⟨smallEtaleDirectImageIdIso.{u, w} X⟩, ⟨smallEtaleInverseImageIdIso.{u, w} X⟩,
      (fun Q Q' τ => smallEtaleDirectImageIdIso_naturality.{u, w} X τ),
      (fun Q Q' τ => smallEtaleInverseImageIdIso_naturality.{u, w} X τ),
      smallEtaleInverseImageIdIso_mate.{u, w} X,
      (fun Q => smallEtaleInverseImageIdIso_unit.{u, w} X Q),
      (fun R => smallEtaleInverseImageIdIso_counit.{u, w} X R)⟩
  · intro X Y Z f g
    dsimp only [SmallEtalePairCoherence]
    exact ⟨⟨smallEtaleDirectImageCompIso.{u, w} f g⟩, ⟨smallEtaleInverseImageCompIso.{u, w} f g⟩,
      (fun Q Q' τ => smallEtaleDirectImageCompIso_naturality.{u, w} f g τ),
      (fun Q Q' τ => smallEtaleInverseImageCompIso_naturality.{u, w} f g τ),
      smallEtaleInverseImageCompIso_mate.{u, w} f g,
      (fun Q => smallEtaleInverseImageCompIso_unit.{u, w} f g Q),
      (fun R => smallEtaleInverseImageCompIso_counit.{u, w} f g R),
      (fun fg hfg => ⟨smallEtaleDirectImageCompTo_eq.{u, w} f g fg hfg,
        smallEtaleInverseImageCompTo_eq.{u, w} f g fg hfg⟩)⟩
  · intro X Y f
    exact ⟨smallEtaleDirectImage_comp_id.{u, w} f, smallEtaleDirectImage_id_comp.{u, w} f,
      smallEtaleInverseImage_comp_id.{u, w} f, smallEtaleInverseImage_id_comp.{u, w} f⟩
  · intro X Y Z T f g h
    exact ⟨smallEtaleDirectImage_assoc.{u, w} f g h, smallEtaleInverseImage_assoc.{u, w} f g h⟩

end AlgebraicGeometry.Scheme.DerivedSections
