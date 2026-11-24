/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FunctorSequencePrecomposition
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeWaldhausen
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeIsoCorners

/-!
# Actual zero-source and zero-quotient functor families

A whole functor with zero values supplies the original zero legs in a
cofiber sequence of arbitrary functors. Both actual rows are admitted
by the general Waldhausen zero and pushout axioms. The original whole
source, middle, and quotient functors are retained by the universal lift.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe vB uB vC uC

namespace CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

variable (C : Type uC) [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

private theorem zeroSourceCofiber {Z Y : C} (hZ : IsZero Z) (i : Z ⟶ Y) :
    IsCofiberSequence i (𝟙 Y) := by
  let e : Z ≅ (0 : C) := hZ.isoZero
  have hZero : IsCofibration (e.inv ≫ i) := WaldhausenCategoryWithoutGluing.zero_isCofibration _ _
  have hI : IsCofibration i := by
    have hPre := MorphismProperty.RespectsIso.precomp
      (WaldhausenCategoryWithoutGluing.cofibrations (C := C)) e.hom _ hZero
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hPre
  let z : Z ⟶ (0 : C) := hZ.to_ (0 : C)
  let q : (0 : C) ⟶ Y := (isZero_zero C).to_ Y
  let : IsIso z := IsZero.isIso hZ (isZero_zero C) z
  exact ⟨hI, z, q, IsPushout.of_horiz_isIso ⟨hZ.eq_of_src _ _⟩⟩

private theorem zeroQuotientCofiber {Y Z : C} (hZ : IsZero Z) (p : Y ⟶ Z) :
    IsCofiberSequence (𝟙 Y) p := by
  let z : Y ⟶ (0 : C) := (isZero_zero C).from_ Y
  let q : (0 : C) ⟶ Z := hZ.from_ (0 : C)
  let : IsIso q := IsZero.isIso (isZero_zero C) hZ q
  exact ⟨(WaldhausenCategoryWithoutGluing.cofibrations (C := C)).id_mem Y, z, q,
    IsPushout.of_vert_isIso ⟨hZ.eq_of_tgt _ _⟩⟩

variable {B : Type uB} [Category.{vB} B] (Z G : B ⥤ C) (hZ : ∀ X : B, IsZero (Z.obj X))

/-- The original unique zero-source natural transformation for a whole
zero-valued functor and an arbitrary target functor. -/
noncomputable def pointwiseZeroSourceArrow : Z ⟶ G where
  app X := (hZ X).to_ (G.obj X)
  naturality {X _Y} _f := (hZ X).eq_of_src _ _

/-- The original unique zero-quotient natural transformation for an
arbitrary source functor and a whole zero-valued target functor. -/
noncomputable def pointwiseZeroQuotientArrow : G ⟶ Z where
  app X := (hZ X).from_ (G.obj X)
  naturality {_X Y} _f := (hZ Y).eq_of_tgt _ _

/-- The entire original Z-to-G-to-G cofiber functor sequence for every
zero-valued Z, using only the general Waldhausen axioms. -/
noncomputable def zeroSourceFunctorSequence : B ⥤ CofiberSequenceCategory C :=
  cofiberFunctorSequenceLift Z G G (pointwiseZeroSourceArrow C Z G hZ) (𝟙 G)
    (fun X => zeroSourceCofiber C (hZ X) ((pointwiseZeroSourceArrow C Z G hZ).app X))

/-- The entire original G-to-G-to-Z cofiber functor sequence for every
zero-valued Z, using only the general Waldhausen axioms. -/
noncomputable def zeroQuotientFunctorSequence : B ⥤ CofiberSequenceCategory C :=
  cofiberFunctorSequenceLift G G Z (𝟙 G) (pointwiseZeroQuotientArrow C Z G hZ)
    (fun X => zeroQuotientCofiber C (hZ X) ((pointwiseZeroQuotientArrow C Z G hZ).app X))

/-- The whole source of the original zeroSource functor family is Z. -/
theorem zeroSourceFunctorSequence_source :
    zeroSourceFunctorSequence C Z G hZ ⋙ source C = Z := by
  unfold zeroSourceFunctorSequence
  exact cofiberFunctorSequenceLift_source _ _ _ _ _ _

/-- The whole middle of the original zeroSource functor family is G. -/
theorem zeroSourceFunctorSequence_middle :
    zeroSourceFunctorSequence C Z G hZ ⋙ middle C = G := by
  unfold zeroSourceFunctorSequence
  exact cofiberFunctorSequenceLift_middle _ _ _ _ _ _

/-- The whole quotient of the original zeroSource functor family is G. -/
theorem zeroSourceFunctorSequence_quotient :
    zeroSourceFunctorSequence C Z G hZ ⋙ quotient C = G := by
  unfold zeroSourceFunctorSequence
  exact cofiberFunctorSequenceLift_quotient _ _ _ _ _ _

/-- The whole source of the original zeroQuotient functor family is G. -/
theorem zeroQuotientFunctorSequence_source :
    zeroQuotientFunctorSequence C Z G hZ ⋙ source C = G := by
  unfold zeroQuotientFunctorSequence
  exact cofiberFunctorSequenceLift_source _ _ _ _ _ _

/-- The whole middle of the original zeroQuotient functor family is G. -/
theorem zeroQuotientFunctorSequence_middle :
    zeroQuotientFunctorSequence C Z G hZ ⋙ middle C = G := by
  unfold zeroQuotientFunctorSequence
  exact cofiberFunctorSequenceLift_middle _ _ _ _ _ _

/-- The whole quotient of the original zeroQuotient functor family is Z. -/
theorem zeroQuotientFunctorSequence_quotient :
    zeroQuotientFunctorSequence C Z G hZ ⋙ quotient C = Z := by
  unfold zeroQuotientFunctorSequence
  exact cofiberFunctorSequenceLift_quotient _ _ _ _ _ _

/-- Forgetting the zero-source family gives its entire original
natural-transformation diagram, including its identity quotient. -/
theorem zeroSourceFunctorSequence_forget :
    zeroSourceFunctorSequence C Z G hZ ⋙ forget C =
      functorSequenceDiagram Z G G (pointwiseZeroSourceArrow C Z G hZ) (𝟙 G) := by
  unfold zeroSourceFunctorSequence
  exact cofiberFunctorSequenceLift_forget _ _ _ _ _ _

/-- Forgetting the zero-quotient family gives its entire original
natural-transformation diagram, including its identity inclusion. -/
theorem zeroQuotientFunctorSequence_forget :
    zeroQuotientFunctorSequence C Z G hZ ⋙ forget C =
      functorSequenceDiagram G G Z (𝟙 G) (pointwiseZeroQuotientArrow C Z G hZ) := by
  unfold zeroQuotientFunctorSequence
  exact cofiberFunctorSequenceLift_forget _ _ _ _ _ _

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
private theorem propertyOfFunctorEq (P : MorphismProperty C) [P.RespectsIso]
    {F₁ F₂ : B ⥤ C} (p : F₁ = F₂) {X Y : B} (f : X ⟶ Y) (h : P (F₂.map f)) :
    P (F₁.map f) := by
  have hPre : P (eqToHom (Functor.congr_obj p X) ≫ F₂.map f) :=
    MorphismProperty.RespectsIso.precomp P (eqToHom (Functor.congr_obj p X)) _ h
  have hPost : P ((eqToHom (Functor.congr_obj p X) ≫ F₂.map f) ≫
      eqToHom (Functor.congr_obj p Y).symm) :=
    MorphismProperty.RespectsIso.postcomp P (eqToHom (Functor.congr_obj p Y).symm) _ hPre
  rw [Functor.congr_hom p f]
  simpa only [Category.assoc] using hPost

/-- Every actual cofibration component of G yields a genuine relative
cofibration of the whole zero-source family, at the original two zero values. -/
theorem zeroSourceFunctorSequence_map_relativeCofibration {X Y : B} (f : X ⟶ Y)
    (hG : IsCofibration (G.map f)) :
    relativeCofibrations C ((zeroSourceFunctorSequence C Z G hZ).map f) := by
  let F := zeroSourceFunctorSequence C Z G hZ
  have hX : IsZero ((source C).obj (F.obj X)) :=
    (hZ X).of_iso (eqToIso (Functor.congr_obj (zeroSourceFunctorSequence_source C Z G hZ) X))
  have hY : IsZero ((source C).obj (F.obj Y)) :=
    (hZ Y).of_iso (eqToIso (Functor.congr_obj (zeroSourceFunctorSequence_source C Z G hZ) Y))
  let : IsIso ((source C).map (F.map f)) := IsZero.isIso hX hY _
  have hMiddle : IsCofibration ((middle C).map (F.map f)) :=
    propertyOfFunctorEq C (WaldhausenCategoryWithoutGluing.cofibrations (C := C))
      (zeroSourceFunctorSequence_middle C Z G hZ) f hG
  exact relativeCofibrations_of_source_isIso C (F.map f) hMiddle

/-- Every actual cofibration component of G yields the genuine relative
corner of its original zero-quotient family, with the original identity inclusion. -/
theorem zeroQuotientFunctorSequence_map_relativeCofibration {X Y : B} (f : X ⟶ Y)
    (hG : IsCofibration (G.map f)) :
    relativeCofibrations C ((zeroQuotientFunctorSequence C Z G hZ).map f) := by
  let F := zeroQuotientFunctorSequence C Z G hZ
  have hRow : (F.obj X).obj =
      (functorSequenceDiagram G G Z (𝟙 G) (pointwiseZeroQuotientArrow C Z G hZ)).obj X :=
    Functor.congr_obj (zeroQuotientFunctorSequence_forget C Z G hZ) X
  let e : (0 : Fin 3) ⟶ 1 := homOfLE (show (0 : Fin 3) ≤ 1 from by decide)
  have hRight : MorphismProperty.isomorphisms C
      (((functorSequenceDiagram G G Z (𝟙 G)
        (pointwiseZeroQuotientArrow C Z G hZ)).obj X).map e) := by
    change IsIso ((functorSequenceDiagram G G Z (𝟙 G)
      (pointwiseZeroQuotientArrow C Z G hZ)).obj X |>.map' 0 1)
    rw [functorSequenceDiagram_map_zero_one]
    have hId : (𝟙 G : G ⟶ G).app X = 𝟙 (G.obj X) := NatTrans.id_app G X
    rw [hId]
    exact inferInstanceAs (IsIso (𝟙 (G.obj X) : G.obj X ⟶ G.obj X))
  have hLeft : IsIso ((F.obj X).obj.map' 0 1) :=
    propertyOfFunctorEq C (MorphismProperty.isomorphisms C) hRow e hRight
  let : IsIso ((F.obj X).obj.map' 0 1) := hLeft
  have hSource : IsCofibration ((source C).map (F.map f)) :=
    propertyOfFunctorEq C (WaldhausenCategoryWithoutGluing.cofibrations (C := C))
      (zeroQuotientFunctorSequence_source C Z G hZ) f hG
  exact relativeCofibrations_of_inclusion_isIso C (F.map f) hSource

universe vA uA

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- The original whole unique zero-source arrow commutes strictly with
arbitrary precomposition of the original zero-valued and target functors. -/
theorem pointwiseZeroSourceArrow_precomp
    {A : Type uA} [Category.{vA} A] (H : A ⥤ B) :
    Functor.whiskerLeft H (pointwiseZeroSourceArrow C Z G hZ) =
      pointwiseZeroSourceArrow C (H ⋙ Z) (H ⋙ G) (fun X => hZ (H.obj X)) := by
  unfold pointwiseZeroSourceArrow
  rfl

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- The original whole unique zero-quotient arrow commutes strictly with
arbitrary precomposition of the original source and zero-valued functors. -/
theorem pointwiseZeroQuotientArrow_precomp
    {A : Type uA} [Category.{vA} A] (H : A ⥤ B) :
    Functor.whiskerLeft H (pointwiseZeroQuotientArrow C Z G hZ) =
      pointwiseZeroQuotientArrow C (H ⋙ Z) (H ⋙ G) (fun X => hZ (H.obj X)) := by
  unfold pointwiseZeroQuotientArrow
  rfl

/-- Every original zero-source functor family commutes strictly with
arbitrary source precomposition, retaining its whole cofiber diagram. -/
theorem zeroSourceFunctorSequence_precomp
    {A : Type uA} [Category.{vA} A] (H : A ⥤ B) :
    H ⋙ zeroSourceFunctorSequence C Z G hZ =
      zeroSourceFunctorSequence C (H ⋙ Z) (H ⋙ G) (fun X => hZ (H.obj X)) := by
  unfold zeroSourceFunctorSequence
  have hId : Functor.whiskerLeft H (𝟙 G : G ⟶ G) = 𝟙 (H ⋙ G) := by
    apply NatTrans.ext
    funext X
    change (𝟙 G : G ⟶ G).app (H.obj X) = (𝟙 (H ⋙ G) : H ⋙ G ⟶ H ⋙ G).app X
    rw [NatTrans.id_app, NatTrans.id_app]
    change (𝟙 (G.obj (H.obj X)) : G.obj (H.obj X) ⟶ G.obj (H.obj X)) =
      (𝟙 (G.obj (H.obj X)) : G.obj (H.obj X) ⟶ G.obj (H.obj X))
    rfl
  simpa only [pointwiseZeroSourceArrow_precomp, hId] using
    (cofiberFunctorSequenceLift_precomp H Z G G (pointwiseZeroSourceArrow C Z G hZ) (𝟙 G)
      (fun X => zeroSourceCofiber C (hZ X) ((pointwiseZeroSourceArrow C Z G hZ).app X)))

/-- Every original zero-quotient functor family commutes strictly with
arbitrary source precomposition, retaining its whole cofiber diagram. -/
theorem zeroQuotientFunctorSequence_precomp
    {A : Type uA} [Category.{vA} A] (H : A ⥤ B) :
    H ⋙ zeroQuotientFunctorSequence C Z G hZ =
      zeroQuotientFunctorSequence C (H ⋙ Z) (H ⋙ G) (fun X => hZ (H.obj X)) := by
  unfold zeroQuotientFunctorSequence
  have hId : Functor.whiskerLeft H (𝟙 G : G ⟶ G) = 𝟙 (H ⋙ G) := by
    apply NatTrans.ext
    funext X
    change (𝟙 G : G ⟶ G).app (H.obj X) = (𝟙 (H ⋙ G) : H ⋙ G ⟶ H ⋙ G).app X
    rw [NatTrans.id_app, NatTrans.id_app]
    change (𝟙 (G.obj (H.obj X)) : G.obj (H.obj X) ⟶ G.obj (H.obj X)) =
      (𝟙 (G.obj (H.obj X)) : G.obj (H.obj X) ⟶ G.obj (H.obj X))
    rfl
  simpa only [pointwiseZeroQuotientArrow_precomp, hId] using
    (cofiberFunctorSequenceLift_precomp H G G Z (𝟙 G) (pointwiseZeroQuotientArrow C Z G hZ)
      (fun X => zeroQuotientCofiber C (hZ X) ((pointwiseZeroQuotientArrow C Z G hZ).app X)))

end CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory
