/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Waldhausen.ZeroObjectReplacement

/-!
# Clients of the original zero-object replacement

The source and target retain independent object and morphism universes.
Every client starts with the arbitrary original exact functor. Its zero
isomorphism and whole arrow maps supply the actual replacement certificates.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uC vC uD vD uE vE

namespace MathlibExtTest.CategoryTheory.Waldhausen.ZeroObjectReplacementTests

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- The arbitrary original exact functor has its earned exact representative. -/
theorem arbitraryExactRepresentative :
    hF.zeroObjectReplacement.IsWaldhausenExact :=
  hF.zeroObjectReplacement_isWaldhausenExact

/-- The selected source and target zeros have the produced object equality. -/
theorem originalSelectedZero : hF.zeroObjectReplacement.obj (0 : C) = (0 : D) :=
  hF.zeroObjectReplacement_obj_zero

/-- Every original arrow retains the full canonical conjugation formula. -/
theorem originalWholeArrow {X Y : C} (f : X ⟶ Y) :
    hF.zeroObjectReplacement.map f = hF.zeroObjectReplacementIso.inv.app X ≫
      F.map f ≫ hF.zeroObjectReplacementIso.hom.app Y :=
  hF.zeroObjectReplacement_map f

/-- The root comparison is the original unique mapped-zero isomorphism. -/
theorem originalZeroIso :
    hF.zeroObjectReplacementIso.hom.app (0 : C) ≫
        eqToHom hF.zeroObjectReplacement_obj_zero =
      (hF.map_isZero (isZero_zero C)).isoZero.hom :=
  hF.zeroObjectReplacementIso_hom_zero

/-- The representative preserves the actual original pushout square. -/
theorem originalPushout {X Y X' P : C}
    (i : X ⟶ Y) (f : X ⟶ X') (inl : X' ⟶ P) (inr : Y ⟶ P)
    (hi : IsCofibration i) (hP : IsPushout f i inl inr) :
    IsPushout (hF.zeroObjectReplacement.map f) (hF.zeroObjectReplacement.map i)
      (hF.zeroObjectReplacement.map inl) (hF.zeroObjectReplacement.map inr) :=
  hF.zeroObjectReplacement_isWaldhausenExact.map_pushout i f inl inr hi hP

/-- The complete original identity is retained. -/
theorem originalIdentity :
    (Functor.IsWaldhausenExact.id (C := C)).zeroObjectReplacement = 𝟭 C :=
  Functor.IsWaldhausenExact.zeroObjectReplacement_id

variable {E : Type uE} [Category.{vE} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]
variable {K : D ⥤ E} (hK : K.IsWaldhausenExact)

/-- The complete source-first composition component has its original formula. -/
theorem originalComposition (X : C) :
    (hF.zeroObjectReplacementCompIso hK).hom.app X =
      hK.zeroObjectReplacementIso.inv.app (hF.zeroObjectReplacement.obj X) ≫
        K.map (hF.zeroObjectReplacementIso.inv.app X) ≫
          (hF.comp hK).zeroObjectReplacementIso.hom.app X :=
  hF.zeroObjectReplacementCompIso_hom_app hK X

/-- The composition comparison has its actual identity root component. -/
theorem originalCompositionZero :
    eqToHom (hF.zeroObjectReplacement_comp_obj_zero hK).symm ≫
        (hF.zeroObjectReplacementCompIso hK).hom.app (0 : C) ≫
          eqToHom (hF.comp hK).zeroObjectReplacement_obj_zero = 𝟙 (0 : E) :=
  hF.zeroObjectReplacementCompIso_hom_zero hK

end MathlibExtTest.CategoryTheory.Waldhausen.ZeroObjectReplacementTests

end
