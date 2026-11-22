/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.ReplacementProperties
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.LevelHoLaws
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ReplacementHo

/-!
# The actual original source replacements on the constructed level Ho category

All four actions use the original transported cardinal data and the actual
source zero-arrow functors. The weak comparison maps and all formal inverse
morphisms are handled by the constructed source level projection.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable {C : Type uC} [Category.{vC} C]
attribute [local instance] Native.modelCategory

/-- The original source π is inverted by the actual source level projection. -/
theorem isIso_projection_cofibrantReplacementCounit
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    IsIso ((LevelHo.projection e).map ((cofibrantReplacementCounit e).app X)) :=
  Localization.inverts (LevelHo.projection e) (NativePresentation.weakProperty e)
    ((cofibrantReplacementCounit e).app X) (cofibrantReplacementCounit_mem_weakEquivalences e X)

/-- The original source ι is inverted by that same constructed projection. -/
theorem isIso_projection_fibrantReplacementUnit
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    IsIso ((LevelHo.projection e).map ((fibrantReplacementUnit e).app X)) :=
  Localization.inverts (LevelHo.projection e) (NativePresentation.weakProperty e)
    ((fibrantReplacementUnit e).app X) (fibrantReplacementUnit_mem_weakEquivalences e X)

/-- The whole source Q comparison uses its original actual π. -/
def cofibrantReplacementProjectionIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantReplacement e ⋙ LevelHo.projection e ≅ LevelHo.projection e := by
  let α := Functor.whiskerRight (cofibrantReplacementCounit e) (LevelHo.projection e)
  let _ : ∀ X, IsIso (α.app X) := isIso_projection_cofibrantReplacementCounit e
  let _ : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The whole source R comparison uses its original actual ι. -/
def fibrantReplacementProjectionIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.projection e ≅ fibrantReplacement e ⋙ LevelHo.projection e := by
  let α := Functor.whiskerRight (fibrantReplacementUnit e) (LevelHo.projection e)
  let _ : ∀ X, IsIso (α.app X) := isIso_projection_fibrantReplacementUnit e
  let _ : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

theorem cofibrantReplacementProjectionIso_hom_app
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantReplacementProjectionIso e).hom.app X =
      (LevelHo.projection e).map ((cofibrantReplacementCounit e).app X) := rfl

theorem fibrantReplacementProjectionIso_hom_app
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantReplacementProjectionIso e).hom.app X =
      (LevelHo.projection e).map ((fibrantReplacementUnit e).app X) := rfl

/-- Both source replacements use the same original Q and inverse original R arrows. -/
def cofibrantFibrantReplacementProjectionIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantFibrantReplacement e ⋙ LevelHo.projection e ≅ LevelHo.projection e :=
  Functor.isoWhiskerLeft (cofibrantReplacement e) (fibrantReplacementProjectionIso e).symm ≪≫
    cofibrantReplacementProjectionIso e

/-- The reverse source replacement order uses those same actual original arrows. -/
def fibrantCofibrantReplacementProjectionIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantCofibrantReplacement e ⋙ LevelHo.projection e ≅ LevelHo.projection e :=
  Functor.isoWhiskerLeft (fibrantReplacement e) (cofibrantReplacementProjectionIso e) ≪≫
    (fibrantReplacementProjectionIso e).symm

theorem cofibrantFibrantReplacementProjectionIso_hom_app
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantFibrantReplacementProjectionIso e).hom.app X =
      (fibrantReplacementProjectionIso e).inv.app ((cofibrantReplacement e).obj X) ≫
        (LevelHo.projection e).map ((cofibrantReplacementCounit e).app X) := rfl

theorem fibrantCofibrantReplacementProjectionIso_hom_app
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantCofibrantReplacementProjectionIso e).hom.app X =
      (LevelHo.projection e).map
        ((cofibrantReplacementCounit e).app ((fibrantReplacement e).obj X)) ≫
          (fibrantReplacementProjectionIso e).inv.app X := rfl

/-- The original source cofibrantReplacement action followed by its actual projection inverts the
original source weak class. -/
theorem cofibrantReplacementHo_inverts
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (NativePresentation.weakProperty e).IsInvertedBy (cofibrantReplacement e ⋙ LevelHo.projection e)
      :=
  fun _ _ φ hφ => Localization.inverts (LevelHo.projection e) (NativePresentation.weakProperty e)
    ((cofibrantReplacement e).map φ) ((cofibrantReplacement_map_weakEquivalence_iff e φ).2 hφ)

/-- The actual source level Ho action uses the original transported replacement functor. -/
def cofibrantReplacementHo (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.HoCategory e ⥤ LevelHo.HoCategory e :=
  Localization.Construction.lift (cofibrantReplacement e ⋙ LevelHo.projection e)
    (cofibrantReplacementHo_inverts e)

/-- Retain the whole strict source projection equality, including every original map. -/
theorem cofibrantReplacementHo_projection (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.projection e ⋙ cofibrantReplacementHo e = cofibrantReplacement e ⋙ LevelHo.projection e
      :=
  Localization.Construction.fac _ _

/-- The strict construction supplies its own complete lifting comparison. -/
def cofibrantReplacementHoProjectionIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.projection e ⋙ cofibrantReplacementHo e ≅ cofibrantReplacement e ⋙ LevelHo.projection e
      :=
  eqToIso (cofibrantReplacementHo_projection e)
/-- The localization lifting witness for the original source I replacement and its projection. -/
@[instance_reducible]
def cofibrantReplacementHoLifting (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Localization.Lifting (LevelHo.projection e) (NativePresentation.weakProperty e)
      (cofibrantReplacement e ⋙ LevelHo.projection e) (cofibrantReplacementHo e) :=
        ⟨cofibrantReplacementHoProjectionIso e⟩

/-- Lift the actual original source comparison to all source Ho morphisms. -/
def cofibrantReplacementHoIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantReplacementHo e ≅ 𝟭 (LevelHo.HoCategory e) := by
  let _ := cofibrantReplacementHoLifting e
  exact Localization.liftNatIso (LevelHo.projection e) (NativePresentation.weakProperty e)
    (cofibrantReplacement e ⋙ LevelHo.projection e) (LevelHo.projection e)
    (cofibrantReplacementHo e) (𝟭 (LevelHo.HoCategory e)) (cofibrantReplacementProjectionIso e)

theorem cofibrantReplacementHo_map_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (φ : X ⟶ Y) :
    (cofibrantReplacementHo e).map ((LevelHo.projection e).map φ) =
      (LevelHo.projection e).map ((cofibrantReplacement e).map φ) :=
  Functor.congr_hom (cofibrantReplacementHo_projection e) φ

/-- Naturality holds for all source Ho morphisms, including formal inverses. -/
theorem cofibrantReplacementHoIso_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (cofibrantReplacementHo e).map φ ≫ (cofibrantReplacementHoIso e).hom.app Y =
      (cofibrantReplacementHoIso e).hom.app X ≫ φ := (cofibrantReplacementHoIso e).hom.naturality φ

theorem cofibrantReplacementHoIso_inv_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    φ ≫ (cofibrantReplacementHoIso e).inv.app Y =
      (cofibrantReplacementHoIso e).inv.app X ≫ (cofibrantReplacementHo e).map φ :=
        (cofibrantReplacementHoIso e).inv.naturality φ

/-- Each actual original source replacement action is an equivalence of the constructed level Ho
category. -/
theorem cofibrantReplacementHo_isEquivalence (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (cofibrantReplacementHo e).IsEquivalence := Functor.isEquivalence_of_iso
      (cofibrantReplacementHoIso e).symm

/-- The original source fibrantReplacement action followed by its actual projection inverts the
original source weak class. -/
theorem fibrantReplacementHo_inverts
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (NativePresentation.weakProperty e).IsInvertedBy (fibrantReplacement e ⋙ LevelHo.projection e)
      :=
  fun _ _ φ hφ => Localization.inverts (LevelHo.projection e) (NativePresentation.weakProperty e)
    ((fibrantReplacement e).map φ) ((fibrantReplacement_map_weakEquivalence_iff e φ).2 hφ)

/-- The actual source level Ho action uses the original transported replacement functor. -/
def fibrantReplacementHo (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.HoCategory e ⥤ LevelHo.HoCategory e :=
  Localization.Construction.lift (fibrantReplacement e ⋙ LevelHo.projection e)
    (fibrantReplacementHo_inverts e)

/-- Retain the whole strict source projection equality, including every original map. -/
theorem fibrantReplacementHo_projection (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.projection e ⋙ fibrantReplacementHo e = fibrantReplacement e ⋙ LevelHo.projection e :=
  Localization.Construction.fac _ _

/-- The strict construction supplies its own complete lifting comparison. -/
def fibrantReplacementHoProjectionIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.projection e ⋙ fibrantReplacementHo e ≅ fibrantReplacement e ⋙ LevelHo.projection e :=
  eqToIso (fibrantReplacementHo_projection e)
/-- The localization lifting witness for the original source J replacement and its projection. -/
@[instance_reducible]
def fibrantReplacementHoLifting (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Localization.Lifting (LevelHo.projection e) (NativePresentation.weakProperty e)
      (fibrantReplacement e ⋙ LevelHo.projection e) (fibrantReplacementHo e) :=
        ⟨fibrantReplacementHoProjectionIso e⟩

/-- Lift the actual original source comparison to all source Ho morphisms. -/
def fibrantReplacementHoIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantReplacementHo e ≅ 𝟭 (LevelHo.HoCategory e) := by
  let _ := fibrantReplacementHoLifting e
  exact Localization.liftNatIso (LevelHo.projection e) (NativePresentation.weakProperty e)
    (fibrantReplacement e ⋙ LevelHo.projection e) (LevelHo.projection e)
    (fibrantReplacementHo e) (𝟭 (LevelHo.HoCategory e)) (fibrantReplacementProjectionIso e).symm

theorem fibrantReplacementHo_map_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (φ : X ⟶ Y) :
    (fibrantReplacementHo e).map ((LevelHo.projection e).map φ) =
      (LevelHo.projection e).map ((fibrantReplacement e).map φ) :=
  Functor.congr_hom (fibrantReplacementHo_projection e) φ

/-- Naturality holds for all source Ho morphisms, including formal inverses. -/
theorem fibrantReplacementHoIso_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (fibrantReplacementHo e).map φ ≫ (fibrantReplacementHoIso e).hom.app Y =
      (fibrantReplacementHoIso e).hom.app X ≫ φ := (fibrantReplacementHoIso e).hom.naturality φ

theorem fibrantReplacementHoIso_inv_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    φ ≫ (fibrantReplacementHoIso e).inv.app Y =
      (fibrantReplacementHoIso e).inv.app X ≫ (fibrantReplacementHo e).map φ :=
        (fibrantReplacementHoIso e).inv.naturality φ

/-- Each actual original source replacement action is an equivalence of the constructed level Ho
category. -/
theorem fibrantReplacementHo_isEquivalence (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (fibrantReplacementHo e).IsEquivalence := Functor.isEquivalence_of_iso (fibrantReplacementHoIso
      e).symm

/-- The original source cofibrantFibrantReplacement action followed by its actual projection inverts
the original source weak class. -/
theorem cofibrantFibrantReplacementHo_inverts
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (NativePresentation.weakProperty e).IsInvertedBy (cofibrantFibrantReplacement e ⋙
      LevelHo.projection e) :=
  fun _ _ φ hφ => Localization.inverts (LevelHo.projection e) (NativePresentation.weakProperty e)
    ((cofibrantFibrantReplacement e).map φ) ((cofibrantFibrantReplacement_map_weakEquivalence_iff e
      φ).2 hφ)

/-- The actual source level Ho action uses the original transported replacement functor. -/
def cofibrantFibrantReplacementHo (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.HoCategory e ⥤ LevelHo.HoCategory e :=
  Localization.Construction.lift (cofibrantFibrantReplacement e ⋙ LevelHo.projection e)
    (cofibrantFibrantReplacementHo_inverts e)

/-- Retain the whole strict source projection equality, including every original map. -/
theorem cofibrantFibrantReplacementHo_projection (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.projection e ⋙ cofibrantFibrantReplacementHo e = cofibrantFibrantReplacement e ⋙
      LevelHo.projection e :=
  Localization.Construction.fac _ _

/-- The strict construction supplies its own complete lifting comparison. -/
def cofibrantFibrantReplacementHoProjectionIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.projection e ⋙ cofibrantFibrantReplacementHo e ≅ cofibrantFibrantReplacement e ⋙
      LevelHo.projection e :=
  eqToIso (cofibrantFibrantReplacementHo_projection e)
/-- The localization lifting witness for the original source I/J replacement composite. -/
@[instance_reducible]
def cofibrantFibrantReplacementHoLifting (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Localization.Lifting (LevelHo.projection e) (NativePresentation.weakProperty e)
      (cofibrantFibrantReplacement e ⋙ LevelHo.projection e) (cofibrantFibrantReplacementHo e) :=
        ⟨cofibrantFibrantReplacementHoProjectionIso e⟩

/-- Lift the actual original source comparison to all source Ho morphisms. -/
def cofibrantFibrantReplacementHoIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantFibrantReplacementHo e ≅ 𝟭 (LevelHo.HoCategory e) := by
  let _ := cofibrantFibrantReplacementHoLifting e
  exact Localization.liftNatIso (LevelHo.projection e) (NativePresentation.weakProperty e)
    (cofibrantFibrantReplacement e ⋙ LevelHo.projection e) (LevelHo.projection e)
    (cofibrantFibrantReplacementHo e) (𝟭 (LevelHo.HoCategory e))
      (cofibrantFibrantReplacementProjectionIso e)

theorem cofibrantFibrantReplacementHo_map_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (φ : X ⟶ Y) :
    (cofibrantFibrantReplacementHo e).map ((LevelHo.projection e).map φ) =
      (LevelHo.projection e).map ((cofibrantFibrantReplacement e).map φ) :=
  Functor.congr_hom (cofibrantFibrantReplacementHo_projection e) φ

/-- Naturality holds for all source Ho morphisms, including formal inverses. -/
theorem cofibrantFibrantReplacementHoIso_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (cofibrantFibrantReplacementHo e).map φ ≫ (cofibrantFibrantReplacementHoIso e).hom.app Y =
      (cofibrantFibrantReplacementHoIso e).hom.app X ≫ φ := (cofibrantFibrantReplacementHoIso
        e).hom.naturality φ

theorem cofibrantFibrantReplacementHoIso_inv_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    φ ≫ (cofibrantFibrantReplacementHoIso e).inv.app Y =
      (cofibrantFibrantReplacementHoIso e).inv.app X ≫ (cofibrantFibrantReplacementHo e).map φ :=
        (cofibrantFibrantReplacementHoIso e).inv.naturality φ

/-- Each actual original source replacement action is an equivalence of the constructed level Ho
category. -/
theorem cofibrantFibrantReplacementHo_isEquivalence (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v}
  A) :
    (cofibrantFibrantReplacementHo e).IsEquivalence := Functor.isEquivalence_of_iso
      (cofibrantFibrantReplacementHoIso e).symm

/-- The original source fibrantCofibrantReplacement action followed by its actual projection inverts
the original source weak class. -/
theorem fibrantCofibrantReplacementHo_inverts
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (NativePresentation.weakProperty e).IsInvertedBy (fibrantCofibrantReplacement e ⋙
      LevelHo.projection e) :=
  fun _ _ φ hφ => Localization.inverts (LevelHo.projection e) (NativePresentation.weakProperty e)
    ((fibrantCofibrantReplacement e).map φ) ((fibrantCofibrantReplacement_map_weakEquivalence_iff e
      φ).2 hφ)

/-- The actual source level Ho action uses the original transported replacement functor. -/
def fibrantCofibrantReplacementHo (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.HoCategory e ⥤ LevelHo.HoCategory e :=
  Localization.Construction.lift (fibrantCofibrantReplacement e ⋙ LevelHo.projection e)
    (fibrantCofibrantReplacementHo_inverts e)

/-- Retain the whole strict source projection equality, including every original map. -/
theorem fibrantCofibrantReplacementHo_projection (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.projection e ⋙ fibrantCofibrantReplacementHo e = fibrantCofibrantReplacement e ⋙
      LevelHo.projection e :=
  Localization.Construction.fac _ _

/-- The strict construction supplies its own complete lifting comparison. -/
def fibrantCofibrantReplacementHoProjectionIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    LevelHo.projection e ⋙ fibrantCofibrantReplacementHo e ≅ fibrantCofibrantReplacement e ⋙
      LevelHo.projection e :=
  eqToIso (fibrantCofibrantReplacementHo_projection e)
/-- The localization lifting witness for the original source J/I replacement composite. -/
@[instance_reducible]
def fibrantCofibrantReplacementHoLifting (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Localization.Lifting (LevelHo.projection e) (NativePresentation.weakProperty e)
      (fibrantCofibrantReplacement e ⋙ LevelHo.projection e) (fibrantCofibrantReplacementHo e) :=
        ⟨fibrantCofibrantReplacementHoProjectionIso e⟩

/-- Lift the actual original source comparison to all source Ho morphisms. -/
def fibrantCofibrantReplacementHoIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantCofibrantReplacementHo e ≅ 𝟭 (LevelHo.HoCategory e) := by
  let _ := fibrantCofibrantReplacementHoLifting e
  exact Localization.liftNatIso (LevelHo.projection e) (NativePresentation.weakProperty e)
    (fibrantCofibrantReplacement e ⋙ LevelHo.projection e) (LevelHo.projection e)
    (fibrantCofibrantReplacementHo e) (𝟭 (LevelHo.HoCategory e))
      (fibrantCofibrantReplacementProjectionIso e)

theorem fibrantCofibrantReplacementHo_map_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (φ : X ⟶ Y) :
    (fibrantCofibrantReplacementHo e).map ((LevelHo.projection e).map φ) =
      (LevelHo.projection e).map ((fibrantCofibrantReplacement e).map φ) :=
  Functor.congr_hom (fibrantCofibrantReplacementHo_projection e) φ

/-- Naturality holds for all source Ho morphisms, including formal inverses. -/
theorem fibrantCofibrantReplacementHoIso_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (fibrantCofibrantReplacementHo e).map φ ≫ (fibrantCofibrantReplacementHoIso e).hom.app Y =
      (fibrantCofibrantReplacementHoIso e).hom.app X ≫ φ := (fibrantCofibrantReplacementHoIso
        e).hom.naturality φ

theorem fibrantCofibrantReplacementHoIso_inv_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    φ ≫ (fibrantCofibrantReplacementHoIso e).inv.app Y =
      (fibrantCofibrantReplacementHoIso e).inv.app X ≫ (fibrantCofibrantReplacementHo e).map φ :=
        (fibrantCofibrantReplacementHoIso e).inv.naturality φ

/-- Each actual original source replacement action is an equivalence of the constructed level Ho
category. -/
theorem fibrantCofibrantReplacementHo_isEquivalence (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v}
  A) :
    (fibrantCofibrantReplacementHo e).IsEquivalence := Functor.isEquivalence_of_iso
      (fibrantCofibrantReplacementHoIso e).symm

/-- The exact original source π remains the Q Ho comparison at a projected object. -/
theorem cofibrantReplacementHoIso_hom_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantReplacementHoIso e).hom.app ((LevelHo.projection e).obj X) =
      (cofibrantReplacementHoProjectionIso e).hom.app X ≫
        (LevelHo.projection e).map ((cofibrantReplacementCounit e).app X) := by
  rw [cofibrantReplacementHoIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change ((cofibrantReplacementHoProjectionIso e).hom.app X ≫
    (LevelHo.projection e).map ((cofibrantReplacementCounit e).app X)) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The exact original source ι remains the inverse R Ho comparison at a projected object. -/
theorem fibrantReplacementHoIso_inv_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantReplacementHoIso e).inv.app ((LevelHo.projection e).obj X) =
      (LevelHo.projection e).map ((fibrantReplacementUnit e).app X) ≫
        (fibrantReplacementHoProjectionIso e).inv.app X := by
  rw [fibrantReplacementHoIso, Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (LevelHo.projection e).map ((fibrantReplacementUnit e).app X)) ≫
    (fibrantReplacementHoProjectionIso e).inv.app X = _
  exact congrArg (fun f => f ≫ (fibrantReplacementHoProjectionIso e).inv.app X) (Category.id_comp _)

/-- The entire source RQ Ho comparison retains the original inverse ι and π. -/
theorem cofibrantFibrantReplacementHoIso_hom_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantFibrantReplacementHoIso e).hom.app ((LevelHo.projection e).obj X) =
      (cofibrantFibrantReplacementHoProjectionIso e).hom.app X ≫
        ((fibrantReplacementProjectionIso e).inv.app ((cofibrantReplacement e).obj X) ≫
          (LevelHo.projection e).map ((cofibrantReplacementCounit e).app X)) := by
  rw [cofibrantFibrantReplacementHoIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso,
    Functor.rightUnitor_inv_app, Category.comp_id, cofibrantFibrantReplacementProjectionIso_hom_app]

/-- The reverse source QR Ho comparison retains π after R and that same inverse ι. -/
theorem fibrantCofibrantReplacementHoIso_hom_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantCofibrantReplacementHoIso e).hom.app ((LevelHo.projection e).obj X) =
      (fibrantCofibrantReplacementHoProjectionIso e).hom.app X ≫
        ((LevelHo.projection e).map
          ((cofibrantReplacementCounit e).app ((fibrantReplacement e).obj X)) ≫
            (fibrantReplacementProjectionIso e).inv.app X) := by
  rw [fibrantCofibrantReplacementHoIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso,
    Functor.rightUnitor_inv_app, Category.comp_id, fibrantCofibrantReplacementProjectionIso_hom_app]

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement
