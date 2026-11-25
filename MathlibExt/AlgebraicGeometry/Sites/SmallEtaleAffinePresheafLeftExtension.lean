/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleBaseChange
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-! # Common-universe affine-comma presheaf left extension

For every scheme morphism, the original affine étale basis followed by actual
base change gives a functor to the original small étale category. The target
objects are not required to be affine. Its comma diagrams are essentially
small in the common coefficient universe, so every affine presheaf has an
actual pointwise left Kan extension, with its natural presheaf adjunction.

Milne, *Lectures on Étale Cohomology*, §8, p. 60, constructs presheaf inverse
image by these diagrams; the affine-domain size refinement uses §7, p. 51.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The actual original affine basis followed by arbitrary scheme base change. -/
abbrev smallEtaleAffineBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.AffineEtale ⥤ X.Etale :=
  Scheme.AffineEtale.Spec Y ⋙ smallEtaleBaseChange f

/-- The actual affine étale category is small in the common universe. -/
theorem smallEtaleAffineCommonEssentiallySmall (Y : Scheme.{u}) :
    EssentiallySmall.{max u w} Y.AffineEtale := by
  let e := equivSmallModel.{u} Y.AffineEtale
  exact EssentiallySmall.mk'
    (e.trans
      (AsSmall.equiv : SmallModel.{u} Y.AffineEtale ≌
        AsSmall.{w} (SmallModel.{u} Y.AffineEtale)))

private instance commonAffineSmall (Y : Scheme.{u}) :
    EssentiallySmall.{max u w} Y.AffineEtale :=
  smallEtaleAffineCommonEssentiallySmall.{u, w} Y

/-- These are the actual diagrams from an original étale object to the
base change of an original affine étale object. -/
abbrev smallEtaleAffineStructuredComma {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :=
  StructuredArrow V (smallEtaleAffineBaseChange f)

/-- The opposite indexing category appropriate for the presheaf colimit.
An object's arrow unop is precisely `V ⟶ G(U)` on the original site. -/
abbrev smallEtaleAffineComma {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :=
  CostructuredArrow (smallEtaleAffineBaseChange f).op (op V)

/-- Stock structured-arrow smallness applies to every actual diagram. -/
theorem smallEtaleAffineStructuredCommaEssentiallySmall
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :
    EssentiallySmall.{max u w} (smallEtaleAffineStructuredComma f V) := by
  infer_instance

/-- Stock costructured-arrow smallness applies in the same common universe. -/
theorem smallEtaleAffineCommaEssentiallySmall
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :
    EssentiallySmall.{max u w} (smallEtaleAffineComma f V) := by
  infer_instance

/-- The literal diagram of the original affine-presheaf groups. -/
abbrev smallEtaleAffineCommaDiagram {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale) :=
  CostructuredArrow.proj (smallEtaleAffineBaseChange f).op (op V) ⋙ P

/-- Every corresponding colimit exists in the same common-universe group
category; no actual-comma object smallness is assumed. -/
theorem smallEtaleAffineCommaHasColimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :
    HasColimitsOfShape (smallEtaleAffineComma f V) AddCommGrpCat.{max u w} := by
  let : EssentiallySmall.{max u w} (smallEtaleAffineComma f V) :=
    smallEtaleAffineCommaEssentiallySmall.{u, w} f V
  exact hasColimitsOfShape_of_essentiallySmall.{max u w} _ _

/-- All actual comma colimits provide pointwise left extensions for every
affine presheaf, with no certificate among the hypotheses. -/
theorem smallEtaleAffineHasPointwiseLeftKanExtension
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    (smallEtaleAffineBaseChange f).op.HasPointwiseLeftKanExtension P := by
  intro V
  let : HasColimitsOfShape
      (CostructuredArrow (smallEtaleAffineBaseChange f).op V)
      AddCommGrpCat.{max u w} :=
    smallEtaleAffineCommaHasColimits.{u, w} f V.unop
  infer_instance

instance smallEtaleAffineCommaColimit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etaleᵒᵖ) :
    HasColimit (CostructuredArrow.proj (smallEtaleAffineBaseChange f).op V ⋙ P) := by
  let : HasColimitsOfShape
      (CostructuredArrow (smallEtaleAffineBaseChange f).op V)
      AddCommGrpCat.{max u w} :=
    smallEtaleAffineCommaHasColimits.{u, w} f V.unop
  infer_instance

instance smallEtaleAffineLeftKanExtension
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    (smallEtaleAffineBaseChange f).op.HasLeftKanExtension P := by
  let : (smallEtaleAffineBaseChange f).op.HasPointwiseLeftKanExtension P :=
    smallEtaleAffineHasPointwiseLeftKanExtension.{u, w} f P
  exact Functor.HasLeftKanExtension.mk
    ((smallEtaleAffineBaseChange f).op.pointwiseLeftKanExtension P)
    ((smallEtaleAffineBaseChange f).op.pointwiseLeftKanExtensionUnit P)

/-- The stock left-Kan-extension functor for every actual affine presheaf. -/
def smallEtaleAffinePresheafLan {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) ⥤
      (X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :=
  (smallEtaleAffineBaseChange f).op.lan (H := AddCommGrpCat.{max u w})

/-- The natural unit belonging to that one actual presheaf functor. -/
def smallEtaleAffinePresheafLanUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    𝟭 (Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) ⟶
      smallEtaleAffinePresheafLan.{u, w} f ⋙
        (Functor.whiskeringLeft Y.AffineEtaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{max u w}).obj
          (smallEtaleAffineBaseChange f).op :=
  (smallEtaleAffineBaseChange f).op.lanUnit (H := AddCommGrpCat.{max u w})

/-- The natural presheaf adjunction, obtained from the stock Kan provider. -/
def smallEtaleAffinePresheafLanAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleAffinePresheafLan.{u, w} f ⊣
      (Functor.whiskeringLeft Y.AffineEtaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{max u w}).obj
        (smallEtaleAffineBaseChange f).op :=
  (smallEtaleAffineBaseChange f).op.lanAdjunction AddCommGrpCat.{max u w}

/-- The actual comma cocone, whose point is the value of the chosen Kan functor. -/
def smallEtaleAffinePresheafLanCocone {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale) :
    Cocone (smallEtaleAffineCommaDiagram.{u, w} f P V) :=
  (Functor.LeftExtension.mk ((smallEtaleAffinePresheafLan.{u, w} f).obj P)
    ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P)).coconeAt (op V)

/-- This very cocone is a colimit, by the derived pointwise Kan property. -/
def smallEtaleAffinePresheafLanIsColimit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale) :
    IsColimit (smallEtaleAffinePresheafLanCocone.{u, w} f P V) :=
  (smallEtaleAffineBaseChange f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P (op V)

/-- The canonical value comparison with the colimit of the same actual groups. -/
def smallEtaleAffinePresheafLanObjIsoColimit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale) :
    ((smallEtaleAffinePresheafLan.{u, w} f).obj P).obj (op V) ≅
      colimit (smallEtaleAffineCommaDiagram.{u, w} f P V) :=
  (smallEtaleAffineBaseChange f).op.leftKanExtensionObjIsoColimit P (op V)

/-- Each actual colimit inclusion is identified with the prescribed unit
component followed by the actual Kan restriction. -/
theorem smallEtaleAffinePresheafLan_ι_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale)
    (j : smallEtaleAffineComma f V) :
    colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).inv =
      ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
        ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map j.hom := by
  exact (smallEtaleAffineBaseChange f).op.ι_leftKanExtensionObjIsoColimit_inv P (op V) j

/-- The canonical forward comparison has the original colimit inclusion value. -/
theorem smallEtaleAffinePresheafLan_ι_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale)
    (j : smallEtaleAffineComma f V) :
    ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
        ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map j.hom ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
      colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j := by
  exact (smallEtaleAffineBaseChange f).op.ι_leftKanExtensionObjIsoColimit_hom P (op V) j

/-- Restriction is the actual colimit map induced by postcomposition of the
same comma arrows with the original étale map. -/
theorem smallEtaleAffinePresheafLan_restriction_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w})
    {V W : X.Etale} (g : V ⟶ W) (j : smallEtaleAffineComma f W) :
    colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P W) j ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P W).inv ≫
        ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map g.op ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
      colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V)
        ((CostructuredArrow.map g.op).obj j) := by
  have h :
      ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map (j.hom ≫ g.op) ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
        colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V)
          ((CostructuredArrow.map g.op).obj j) :=
    smallEtaleAffinePresheafLan_ι_hom.{u, w} f P V ((CostructuredArrow.map g.op).obj j)
  rw [← Category.assoc, smallEtaleAffinePresheafLan_ι_inv.{u, w} f P W j]
  simpa only [Functor.map_comp, Category.assoc] using h

/-- Every affine-presheaf morphism induces the actual corresponding colimit map. -/
theorem smallEtaleAffinePresheafLan_map_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {P P' : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}} (α : P ⟶ P')
    (V : X.Etale) (j : smallEtaleAffineComma f V) :
    colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).inv ≫
        ((smallEtaleAffinePresheafLan.{u, w} f).map α).app (op V) ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P' V).hom =
      α.app j.left ≫ colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P' V) j := by
  have hUnit :
      ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).map α).app
            ((smallEtaleAffineBaseChange f).op.obj j.left) =
        α.app j.left ≫ ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P').app j.left :=
    (congr_app ((smallEtaleAffinePresheafLanUnit.{u, w} f).naturality α) j.left).symm
  rw [← Category.assoc, smallEtaleAffinePresheafLan_ι_inv.{u, w} f P V j]
  rw [Category.assoc,
    ((smallEtaleAffinePresheafLan.{u, w} f).map α).naturality_assoc j.hom]
  rw [← Category.assoc, hUnit]
  simpa only [Category.assoc] using congrArg (fun k => α.app j.left ≫ k)
    (smallEtaleAffinePresheafLan_ι_hom.{u, w} f P' V j)

/-- The natural Hom equivalence for every actual target presheaf. -/
def smallEtaleAffinePresheafLanHomEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w})
    (Q : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    ((smallEtaleAffinePresheafLan.{u, w} f).obj P ⟶ Q) ≃
      (P ⟶ (smallEtaleAffineBaseChange f).op ⋙ Q) :=
  (smallEtaleAffinePresheafLanAdjunction.{u, w} f).homEquiv P Q

/-- The whole construction uses one actual left-extension functor: the same
comma diagrams give its pointwise colimits, restriction and morphism maps,
and its natural presheaf adjunction, for every original affine presheaf. -/
theorem original_small_etale_affine_presheaf_left_extension
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ V : X.Etale,
      EssentiallySmall.{max u w} (smallEtaleAffineStructuredComma f V) ∧
      EssentiallySmall.{max u w} (smallEtaleAffineComma f V) ∧
      HasColimitsOfShape (smallEtaleAffineComma f V) AddCommGrpCat.{max u w}) ∧
    (∀ (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale),
      Nonempty (IsColimit (smallEtaleAffinePresheafLanCocone.{u, w} f P V))) ∧
    Nonempty (smallEtaleAffinePresheafLan.{u, w} f ⊣
      (Functor.whiskeringLeft Y.AffineEtaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{max u w}).obj
        (smallEtaleAffineBaseChange f).op) ∧
    (∀ (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale)
        (j : smallEtaleAffineComma f V),
      ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map j.hom ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
        colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j) ∧
    (∀ (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w})
        (V W : X.Etale) (g : V ⟶ W) (j : smallEtaleAffineComma f W),
      colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P W) j ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P W).inv ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map g.op ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
        colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V)
          ((CostructuredArrow.map g.op).obj j)) ∧
    ∀ (P P' : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (α : P ⟶ P')
      (V : X.Etale) (j : smallEtaleAffineComma f V),
      colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).inv ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).map α).app (op V) ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P' V).hom =
        α.app j.left ≫ colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P' V) j := by
  refine ⟨?_, ?_, ⟨smallEtaleAffinePresheafLanAdjunction.{u, w} f⟩, ?_, ?_, ?_⟩
  · intro V
    exact ⟨smallEtaleAffineStructuredCommaEssentiallySmall.{u, w} f V,
      smallEtaleAffineCommaEssentiallySmall.{u, w} f V,
      smallEtaleAffineCommaHasColimits.{u, w} f V⟩
  · intro P V
    exact ⟨smallEtaleAffinePresheafLanIsColimit.{u, w} f P V⟩
  · intro P V j
    exact smallEtaleAffinePresheafLan_ι_hom.{u, w} f P V j
  · intro P V W g j
    exact smallEtaleAffinePresheafLan_restriction_ι.{u, w} f P g j
  · intro P P' α V j
    exact smallEtaleAffinePresheafLan_map_ι.{u, w} f α V j

end AlgebraicGeometry.Scheme.DerivedSections
