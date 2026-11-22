/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.ReplacementHo

/-!
# Original source/native replacement transport on the whole level Ho category

Every comparison is induced by the actual original source zero-arrow and
same-cardinal factorization comparisons. Both directions act on all Ho
morphisms and retain the literal original π and ι components.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable {C : Type uC} [Category.{vC} C]
attribute [local instance] Native.modelCategory

private theorem comparisonLeft_projection
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (F : C ⥤ C) (FHo : LevelHo.HoCategory e ⥤ LevelHo.HoCategory e)
    (hF : LevelHo.projection e ⋙ FHo = F ⋙ LevelHo.projection e) :
    LevelHo.projection e ⋙ (FHo ⋙ LevelHo.forward e) =
      (F ⋙ e.functor) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := by
  calc
    LevelHo.projection e ⋙ (FHo ⋙ LevelHo.forward e) =
        (LevelHo.projection e ⋙ FHo) ⋙ LevelHo.forward e := rfl
    _ = (F ⋙ LevelHo.projection e) ⋙ LevelHo.forward e := by rw [hF]
    _ = F ⋙ (LevelHo.projection e ⋙ LevelHo.forward e) := rfl
    _ = F ⋙ (e.functor ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) := by
      rw [LevelHo.forward_projection]
    _ = (F ⋙ e.functor) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := rfl

private theorem comparisonRight_projection
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (G : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (GHo : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
      HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (hG : toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ GHo =
      G ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    LevelHo.projection e ⋙ (LevelHo.forward e ⋙ GHo) =
      (e.functor ⋙ G) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := by
  calc
    LevelHo.projection e ⋙ (LevelHo.forward e ⋙ GHo) =
        (LevelHo.projection e ⋙ LevelHo.forward e) ⋙ GHo := rfl
    _ = (e.functor ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) ⋙ GHo := by
      rw [LevelHo.forward_projection]
    _ = e.functor ⋙ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ GHo) := rfl
    _ = e.functor ⋙ (G ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) := by rw [hG]
    _ = (e.functor ⋙ G) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := rfl

/-- This internal universal-property step receives strict projection equalities,
not model or replacement dictionaries. Every public application below supplies
the already constructed original replacement actions and their actual equalities. -/
private def comparisonHo
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (F : C ⥤ C)
    (G : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (FHo : LevelHo.HoCategory e ⥤ LevelHo.HoCategory e)
    (GHo : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
      HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (hF : LevelHo.projection e ⋙ FHo = F ⋙ LevelHo.projection e)
    (hG : toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ GHo =
      G ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (α : F ⋙ e.functor ≅ e.functor ⋙ G) :
    FHo ⋙ LevelHo.forward e ≅ LevelHo.forward e ⋙ GHo := by
  let _ : Localization.Lifting (LevelHo.projection e) (NativePresentation.weakProperty e)
      ((F ⋙ e.functor) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (FHo ⋙ LevelHo.forward e) := ⟨eqToIso (comparisonLeft_projection e F FHo hF)⟩
  let _ : Localization.Lifting (LevelHo.projection e) (NativePresentation.weakProperty e)
      ((e.functor ⋙ G) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (LevelHo.forward e ⋙ GHo) := ⟨eqToIso (comparisonRight_projection e G GHo hG)⟩
  exact Localization.liftNatIso (LevelHo.projection e) (NativePresentation.weakProperty e)
    ((F ⋙ e.functor) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    ((e.functor ⋙ G) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (FHo ⋙ LevelHo.forward e) (LevelHo.forward e ⋙ GHo)
    (Functor.isoWhiskerRight α (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)))

/-- The whole actual original source/native cofibrantReplacement comparison on level Ho. -/
def cofibrantReplacementHoComparisonIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantReplacementHo e ⋙ LevelHo.forward e ≅
      LevelHo.forward e ⋙ Native.Replacement.cofibrantReplacementHo (B := B) (A := A) :=
  comparisonHo e (cofibrantReplacement e) (Native.Replacement.cofibrantReplacement (B := B) (A :=
    A))
    (cofibrantReplacementHo e) (Native.Replacement.cofibrantReplacementHo (B := B) (A := A))
    (cofibrantReplacementHo_projection e) Native.Replacement.cofibrantReplacementHo_projection
    (cofibrantReplacementComparisonIso e)

/-- Retain the exact original full replacement comparison at every projected source object. -/
theorem cofibrantReplacementHoComparisonIso_hom_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantReplacementHoComparisonIso e).hom.app ((LevelHo.projection e).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        ((cofibrantReplacementComparisonIso e).hom.app X) := by
  rw [cofibrantReplacementHoComparisonIso, comparisonHo,
    Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
    ((cofibrantReplacementComparisonIso e).hom.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The inverse retains the full original inverse replacement comparison. -/
theorem cofibrantReplacementHoComparisonIso_inv_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantReplacementHoComparisonIso e).inv.app ((LevelHo.projection e).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        ((cofibrantReplacementComparisonIso e).inv.app X) := by
  rw [cofibrantReplacementHoComparisonIso, comparisonHo,
    Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
    ((cofibrantReplacementComparisonIso e).inv.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The complete comparison is natural for every source Ho morphism. -/
theorem cofibrantReplacementHoComparisonIso_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (cofibrantReplacementHo e ⋙ LevelHo.forward e).map φ ≫ (cofibrantReplacementHoComparisonIso
      e).hom.app Y =
      (cofibrantReplacementHoComparisonIso e).hom.app X ≫
        (LevelHo.forward e ⋙ Native.Replacement.cofibrantReplacementHo (B := B) (A := A)).map φ :=
  (cofibrantReplacementHoComparisonIso e).hom.naturality φ

theorem cofibrantReplacementHoComparisonIso_inv_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (LevelHo.forward e ⋙ Native.Replacement.cofibrantReplacementHo (B := B) (A := A)).map φ ≫
      (cofibrantReplacementHoComparisonIso e).inv.app Y =
        (cofibrantReplacementHoComparisonIso e).inv.app X ≫ (cofibrantReplacementHo e ⋙
          LevelHo.forward e).map φ :=
  (cofibrantReplacementHoComparisonIso e).inv.naturality φ

/-- Conjugate through the actual source/native Ho equivalence, retaining its actual inverse. -/
def cofibrantReplacementHoConjugacyIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantReplacementHo e ≅ LevelHo.forward e ⋙
      Native.Replacement.cofibrantReplacementHo (B := B) (A := A) ⋙ LevelHo.inverse e :=
  Functor.isoWhiskerLeft (cofibrantReplacementHo e) (LevelHo.unitIso e) ≪≫
    Functor.isoWhiskerRight (cofibrantReplacementHoComparisonIso e) (LevelHo.inverse e)

/-- The whole actual original source/native fibrantReplacement comparison on level Ho. -/
def fibrantReplacementHoComparisonIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantReplacementHo e ⋙ LevelHo.forward e ≅
      LevelHo.forward e ⋙ Native.Replacement.fibrantReplacementHo (B := B) (A := A) :=
  comparisonHo e (fibrantReplacement e) (Native.Replacement.fibrantReplacement (B := B) (A := A))
    (fibrantReplacementHo e) (Native.Replacement.fibrantReplacementHo (B := B) (A := A))
    (fibrantReplacementHo_projection e) Native.Replacement.fibrantReplacementHo_projection
    (fibrantReplacementComparisonIso e)

/-- Retain the exact original full replacement comparison at every projected source object. -/
theorem fibrantReplacementHoComparisonIso_hom_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantReplacementHoComparisonIso e).hom.app ((LevelHo.projection e).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        ((fibrantReplacementComparisonIso e).hom.app X) := by
  rw [fibrantReplacementHoComparisonIso, comparisonHo,
    Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
    ((fibrantReplacementComparisonIso e).hom.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The inverse retains the full original inverse replacement comparison. -/
theorem fibrantReplacementHoComparisonIso_inv_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantReplacementHoComparisonIso e).inv.app ((LevelHo.projection e).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        ((fibrantReplacementComparisonIso e).inv.app X) := by
  rw [fibrantReplacementHoComparisonIso, comparisonHo,
    Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
    ((fibrantReplacementComparisonIso e).inv.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The complete comparison is natural for every source Ho morphism. -/
theorem fibrantReplacementHoComparisonIso_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (fibrantReplacementHo e ⋙ LevelHo.forward e).map φ ≫ (fibrantReplacementHoComparisonIso
      e).hom.app Y =
      (fibrantReplacementHoComparisonIso e).hom.app X ≫
        (LevelHo.forward e ⋙ Native.Replacement.fibrantReplacementHo (B := B) (A := A)).map φ :=
  (fibrantReplacementHoComparisonIso e).hom.naturality φ

theorem fibrantReplacementHoComparisonIso_inv_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (LevelHo.forward e ⋙ Native.Replacement.fibrantReplacementHo (B := B) (A := A)).map φ ≫
      (fibrantReplacementHoComparisonIso e).inv.app Y =
        (fibrantReplacementHoComparisonIso e).inv.app X ≫ (fibrantReplacementHo e ⋙ LevelHo.forward
          e).map φ :=
  (fibrantReplacementHoComparisonIso e).inv.naturality φ

/-- Conjugate through the actual source/native Ho equivalence, retaining its actual inverse. -/
def fibrantReplacementHoConjugacyIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantReplacementHo e ≅ LevelHo.forward e ⋙
      Native.Replacement.fibrantReplacementHo (B := B) (A := A) ⋙ LevelHo.inverse e :=
  Functor.isoWhiskerLeft (fibrantReplacementHo e) (LevelHo.unitIso e) ≪≫
    Functor.isoWhiskerRight (fibrantReplacementHoComparisonIso e) (LevelHo.inverse e)

/-- The whole actual original source/native cofibrantFibrantReplacement comparison on level Ho. -/
def cofibrantFibrantReplacementHoComparisonIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantFibrantReplacementHo e ⋙ LevelHo.forward e ≅
      LevelHo.forward e ⋙ Native.Replacement.cofibrantFibrantReplacementHo (B := B) (A := A) :=
  comparisonHo e (cofibrantFibrantReplacement e) (Native.Replacement.cofibrantFibrantReplacement (B
    := B) (A := A))
    (cofibrantFibrantReplacementHo e) (Native.Replacement.cofibrantFibrantReplacementHo (B := B) (A
      := A))
    (cofibrantFibrantReplacementHo_projection e)
      Native.Replacement.cofibrantFibrantReplacementHo_projection
    (cofibrantFibrantReplacementComparisonIso e)

/-- Retain the exact original full replacement comparison at every projected source object. -/
theorem cofibrantFibrantReplacementHoComparisonIso_hom_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantFibrantReplacementHoComparisonIso e).hom.app ((LevelHo.projection e).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        ((cofibrantFibrantReplacementComparisonIso e).hom.app X) := by
  rw [cofibrantFibrantReplacementHoComparisonIso, comparisonHo,
    Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
    ((cofibrantFibrantReplacementComparisonIso e).hom.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The inverse retains the full original inverse replacement comparison. -/
theorem cofibrantFibrantReplacementHoComparisonIso_inv_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantFibrantReplacementHoComparisonIso e).inv.app ((LevelHo.projection e).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        ((cofibrantFibrantReplacementComparisonIso e).inv.app X) := by
  rw [cofibrantFibrantReplacementHoComparisonIso, comparisonHo,
    Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
    ((cofibrantFibrantReplacementComparisonIso e).inv.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The complete comparison is natural for every source Ho morphism. -/
theorem cofibrantFibrantReplacementHoComparisonIso_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (cofibrantFibrantReplacementHo e ⋙ LevelHo.forward e).map φ ≫
      (cofibrantFibrantReplacementHoComparisonIso e).hom.app Y =
      (cofibrantFibrantReplacementHoComparisonIso e).hom.app X ≫
        (LevelHo.forward e ⋙ Native.Replacement.cofibrantFibrantReplacementHo (B := B) (A := A)).map
          φ :=
  (cofibrantFibrantReplacementHoComparisonIso e).hom.naturality φ

theorem cofibrantFibrantReplacementHoComparisonIso_inv_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (LevelHo.forward e ⋙ Native.Replacement.cofibrantFibrantReplacementHo (B := B) (A := A)).map φ ≫
      (cofibrantFibrantReplacementHoComparisonIso e).inv.app Y =
        (cofibrantFibrantReplacementHoComparisonIso e).inv.app X ≫ (cofibrantFibrantReplacementHo e
          ⋙ LevelHo.forward e).map φ :=
  (cofibrantFibrantReplacementHoComparisonIso e).inv.naturality φ

/-- Conjugate through the actual source/native Ho equivalence, retaining its actual inverse. -/
def cofibrantFibrantReplacementHoConjugacyIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantFibrantReplacementHo e ≅ LevelHo.forward e ⋙
      Native.Replacement.cofibrantFibrantReplacementHo (B := B) (A := A) ⋙ LevelHo.inverse e :=
  Functor.isoWhiskerLeft (cofibrantFibrantReplacementHo e) (LevelHo.unitIso e) ≪≫
    Functor.isoWhiskerRight (cofibrantFibrantReplacementHoComparisonIso e) (LevelHo.inverse e)

/-- The whole actual original source/native fibrantCofibrantReplacement comparison on level Ho. -/
def fibrantCofibrantReplacementHoComparisonIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantCofibrantReplacementHo e ⋙ LevelHo.forward e ≅
      LevelHo.forward e ⋙ Native.Replacement.fibrantCofibrantReplacementHo (B := B) (A := A) :=
  comparisonHo e (fibrantCofibrantReplacement e) (Native.Replacement.fibrantCofibrantReplacement (B
    := B) (A := A))
    (fibrantCofibrantReplacementHo e) (Native.Replacement.fibrantCofibrantReplacementHo (B := B) (A
      := A))
    (fibrantCofibrantReplacementHo_projection e)
      Native.Replacement.fibrantCofibrantReplacementHo_projection
    (fibrantCofibrantReplacementComparisonIso e)

/-- Retain the exact original full replacement comparison at every projected source object. -/
theorem fibrantCofibrantReplacementHoComparisonIso_hom_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantCofibrantReplacementHoComparisonIso e).hom.app ((LevelHo.projection e).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        ((fibrantCofibrantReplacementComparisonIso e).hom.app X) := by
  rw [fibrantCofibrantReplacementHoComparisonIso, comparisonHo,
    Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
    ((fibrantCofibrantReplacementComparisonIso e).hom.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The inverse retains the full original inverse replacement comparison. -/
theorem fibrantCofibrantReplacementHoComparisonIso_inv_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantCofibrantReplacementHoComparisonIso e).inv.app ((LevelHo.projection e).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        ((fibrantCofibrantReplacementComparisonIso e).inv.app X) := by
  rw [fibrantCofibrantReplacementHoComparisonIso, comparisonHo,
    Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
    ((fibrantCofibrantReplacementComparisonIso e).inv.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The complete comparison is natural for every source Ho morphism. -/
theorem fibrantCofibrantReplacementHoComparisonIso_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (fibrantCofibrantReplacementHo e ⋙ LevelHo.forward e).map φ ≫
      (fibrantCofibrantReplacementHoComparisonIso e).hom.app Y =
      (fibrantCofibrantReplacementHoComparisonIso e).hom.app X ≫
        (LevelHo.forward e ⋙ Native.Replacement.fibrantCofibrantReplacementHo (B := B) (A := A)).map
          φ :=
  (fibrantCofibrantReplacementHoComparisonIso e).hom.naturality φ

theorem fibrantCofibrantReplacementHoComparisonIso_inv_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : LevelHo.HoCategory e} (φ : X ⟶ Y) :
    (LevelHo.forward e ⋙ Native.Replacement.fibrantCofibrantReplacementHo (B := B) (A := A)).map φ ≫
      (fibrantCofibrantReplacementHoComparisonIso e).inv.app Y =
        (fibrantCofibrantReplacementHoComparisonIso e).inv.app X ≫ (fibrantCofibrantReplacementHo e
          ⋙ LevelHo.forward e).map φ :=
  (fibrantCofibrantReplacementHoComparisonIso e).inv.naturality φ

/-- Conjugate through the actual source/native Ho equivalence, retaining its actual inverse. -/
def fibrantCofibrantReplacementHoConjugacyIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantCofibrantReplacementHo e ≅ LevelHo.forward e ⋙
      Native.Replacement.fibrantCofibrantReplacementHo (B := B) (A := A) ⋙ LevelHo.inverse e :=
  Functor.isoWhiskerLeft (fibrantCofibrantReplacementHo e) (LevelHo.unitIso e) ≪≫
    Functor.isoWhiskerRight (fibrantCofibrantReplacementHoComparisonIso e) (LevelHo.inverse e)

/-- The original source π square is retained after the actual Ho equivalence. -/
theorem cofibrantReplacementHoComparisonIso_p_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantReplacementHoComparisonIso e).hom.app ((LevelHo.projection e).obj X) ≫
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (Native.Replacement.cofibrantReplacementCounit.app (e.functor.obj X)) =
      (LevelHo.forward e).map
        ((LevelHo.projection e).map ((cofibrantReplacementCounit e).app X)) := by
  rw [cofibrantReplacementHoComparisonIso_hom_projected,
    ← (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map_comp,
    cofibrantReplacementComparisonIso_p]
  exact (LevelHo.forward_map_projected e ((cofibrantReplacementCounit e).app X)).symm

/-- The original source ι square is retained after the same actual Ho equivalence. -/
theorem fibrantReplacementHoComparisonIso_i_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (LevelHo.forward e).map ((LevelHo.projection e).map ((fibrantReplacementUnit e).app X)) ≫
      (fibrantReplacementHoComparisonIso e).hom.app ((LevelHo.projection e).obj X) =
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
          (Native.Replacement.fibrantReplacementUnit.app (e.functor.obj X)) := by
  rw [LevelHo.forward_map_projected, fibrantReplacementHoComparisonIso_hom_projected,
    ← (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map_comp,
    fibrantReplacementComparisonIso_i]

/-- The original I first arrow also keeps the exact native zero comparison after projection. -/
theorem cofibrantReplacementHoComparisonIso_i_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (LevelHo.forward e).map
        ((LevelHo.projection e).map ((initialToCofibrantReplacement e).app X)) ≫
      (cofibrantReplacementHoComparisonIso e).hom.app ((LevelHo.projection e).obj X) =
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map (Zero.comparisonIso
          e).hom ≫
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
            (Native.Replacement.initialToCofibrantReplacement.app (e.functor.obj X)) := by
  rw [LevelHo.forward_map_projected, cofibrantReplacementHoComparisonIso_hom_projected,
    ← (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map_comp,
    cofibrantReplacementComparisonIso_i]
  exact (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map_comp _ _

/-- The original J second arrow keeps that same actual zero comparison after projection. -/
theorem fibrantReplacementHoComparisonIso_p_projected
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantReplacementHoComparisonIso e).hom.app ((LevelHo.projection e).obj X) ≫
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (Native.Replacement.fibrantReplacementToZero.app (e.functor.obj X)) =
      (LevelHo.forward e).map
        ((LevelHo.projection e).map ((fibrantReplacementToZero e).app X)) ≫
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map (Zero.comparisonIso
            e).hom := by
  rw [fibrantReplacementHoComparisonIso_hom_projected,
    ← (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map_comp,
    fibrantReplacementComparisonIso_p,
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map_comp,
    LevelHo.forward_map_projected]

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement
