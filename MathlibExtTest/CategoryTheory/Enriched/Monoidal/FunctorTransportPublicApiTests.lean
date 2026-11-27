/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic

/-!
# Public enriched product and value transport clients

The product clients use four independent plain enriched categories. The transport
clients use a plain enriched source and retain the complete enriched Hom maps.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uA uB uE uF uC uD vD
open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedMonoidalPublicClients

section Products

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {E : Type uE} [EnrichedCategory V E]
  {F : Type uF} [EnrichedCategory V F]
  (L : EnrichedFunctor V A B) (R : EnrichedFunctor V E F)

example (X : A × E) :
    (prodEnrichedFunctor L R).obj X = (L.obj X.1, R.obj X.2) := rfl

example (X Y : A × E) :
    (prodEnrichedFunctor L R).map X Y = L.map X.1 Y.1 ⊗ₘ R.map X.2 Y.2 := rfl

example (X : A × E) :
    eId V X ≫ (prodEnrichedFunctor L R).map X X =
      eId V ((prodEnrichedFunctor L R).obj X) :=
  (prodEnrichedFunctor L R).map_id X

example (X Y Z : A × E) :
    eComp V X Y Z ≫ (prodEnrichedFunctor L R).map X Z =
      ((prodEnrichedFunctor L R).map X Y ⊗ₘ (prodEnrichedFunctor L R).map Y Z) ≫
        eComp V ((prodEnrichedFunctor L R).obj X)
          ((prodEnrichedFunctor L R).obj Y) ((prodEnrichedFunctor L R).obj Z) :=
  (prodEnrichedFunctor L R).map_comp X Y Z

end Products

section Transport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [Category.{vD} D] [EnrichedOrdinaryCategory V D]
  (F : EnrichedFunctor V C D) (Gobj : C → D) (e : ∀ X, F.obj X ≅ Gobj X)

example (X Y : C) :
    (F.ofIsoComponents Gobj e).map X Y =
      F.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom :=
  F.ofIsoComponents_map Gobj e X Y

example (X Y : C) :
    (F.ofIsoComponents Gobj e).map X Y ≫
        (Iso.eHomCongr V (e X) (e Y)).inv = F.map X Y :=
  F.ofIsoComponents_map_inv Gobj e X Y

example (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft V (F.obj X) (e Y).hom =
      (F.ofIsoComponents Gobj e).map X Y ≫
        eHomWhiskerRight V (e X).hom (Gobj Y) :=
  F.ofIsoComponents_naturality Gobj e X Y

theorem iso_hom_app (X : C) :
    (F.ofIsoComponentsIso Gobj e).hom.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).hom) :=
  F.ofIsoComponentsIso_hom_app Gobj e X

theorem iso_inv_app (X : C) :
    (F.ofIsoComponentsIso Gobj e).inv.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).inv) :=
  F.ofIsoComponentsIso_inv_app Gobj e X

theorem iso_hom_component (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofIsoComponentsIso Gobj e).hom.out.app (ForgetEnrichment.of V X))) =
        (e X).hom :=
  F.ofIsoComponentsIso_hom_component Gobj e X

theorem iso_inv_component (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofIsoComponentsIso Gobj e).inv.out.app (ForgetEnrichment.of V X))) =
        (e X).inv :=
  F.ofIsoComponentsIso_inv_component Gobj e X

theorem iso_hom_inv :
    (F.ofIsoComponentsIso Gobj e).hom ≫ (F.ofIsoComponentsIso Gobj e).inv = 𝟙 F :=
  (F.ofIsoComponentsIso Gobj e).hom_inv_id

theorem iso_inv_hom :
    (F.ofIsoComponentsIso Gobj e).inv ≫ (F.ofIsoComponentsIso Gobj e).hom =
      𝟙 (F.ofIsoComponents Gobj e) :=
  (F.ofIsoComponentsIso Gobj e).inv_hom_id

variable [BraidedCategory V]

theorem graded_hom_app (X : C) :
    (F.ofIsoComponentsGraded Gobj e).app X = eHomEquiv V (e X).hom :=
  F.ofIsoComponentsGraded_app Gobj e X

theorem graded_inv_app (X : C) :
    (F.ofIsoComponentsInvGraded Gobj e).app X = eHomEquiv V (e X).inv :=
  F.ofIsoComponentsInvGraded_app Gobj e X

theorem graded_hom_inv (X : C) :
    (λ_ (𝟙_ V)).inv ≫
        ((F.ofIsoComponentsGraded Gobj e).app X ⊗ₘ
          (F.ofIsoComponentsInvGraded Gobj e).app X) ≫
        eComp V (F.obj X) (Gobj X) (F.obj X) = eId V (F.obj X) :=
  F.ofIsoComponentsGraded_comp_inv Gobj e X

theorem graded_inv_hom (X : C) :
    (λ_ (𝟙_ V)).inv ≫
        ((F.ofIsoComponentsInvGraded Gobj e).app X ⊗ₘ
          (F.ofIsoComponentsGraded Gobj e).app X) ≫
        eComp V (Gobj X) (F.obj X) (Gobj X) = eId V (Gobj X) :=
  F.ofIsoComponentsInvGraded_comp_hom Gobj e X

variable
  (s : ∀ X Y : C, (X ⟶[V] Y) ⟶ (Gobj X ⟶[V] Gobj Y))
  (hnat : ∀ X Y,
    (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
          (F.map X Y ⊗ₘ eHomEquiv V (e Y).hom) ≫
        eComp V (F.obj X) (F.obj Y) (Gobj Y) =
      (eHomEquiv V (e X).hom ⊗ₘ s X Y) ≫
        eComp V (F.obj X) (Gobj X) (Gobj Y))

example (X Y : C) : (F.ofRawIsoComponents Gobj s e hnat).map X Y = s X Y :=
  F.ofRawIsoComponents_map Gobj s e hnat X Y

example (X Y : C) :
    (F.ofRawIsoComponents Gobj s e hnat).map X Y ≫
        (Iso.eHomCongr V (e X) (e Y)).inv = F.map X Y :=
  F.ofRawIsoComponents_map_inv Gobj s e hnat X Y

theorem raw_iso_hom_app (X : C) :
    (F.ofRawIsoComponentsIso Gobj s e hnat).hom.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).hom) :=
  F.ofRawIsoComponentsIso_hom_app Gobj s e hnat X

theorem raw_iso_inv_app (X : C) :
    (F.ofRawIsoComponentsIso Gobj s e hnat).inv.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).inv) :=
  F.ofRawIsoComponentsIso_inv_app Gobj s e hnat X

theorem raw_iso_hom_component (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofRawIsoComponentsIso Gobj s e hnat).hom.out.app (ForgetEnrichment.of V X))) =
        (e X).hom :=
  F.ofRawIsoComponentsIso_hom_component Gobj s e hnat X

theorem raw_iso_inv_component (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofRawIsoComponentsIso Gobj s e hnat).inv.out.app (ForgetEnrichment.of V X))) =
        (e X).inv :=
  F.ofRawIsoComponentsIso_inv_component Gobj s e hnat X

theorem raw_iso_hom_inv :
    (F.ofRawIsoComponentsIso Gobj s e hnat).hom ≫
        (F.ofRawIsoComponentsIso Gobj s e hnat).inv = 𝟙 F :=
  (F.ofRawIsoComponentsIso Gobj s e hnat).hom_inv_id

theorem raw_iso_inv_hom :
    (F.ofRawIsoComponentsIso Gobj s e hnat).inv ≫
        (F.ofRawIsoComponentsIso Gobj s e hnat).hom =
      𝟙 (F.ofRawIsoComponents Gobj s e hnat) :=
  (F.ofRawIsoComponentsIso Gobj s e hnat).inv_hom_id

theorem raw_graded_hom_app (X : C) :
    (F.ofRawIsoComponentsGraded Gobj s e hnat).app X = eHomEquiv V (e X).hom :=
  F.ofRawIsoComponentsGraded_app Gobj s e hnat X

theorem raw_graded_inv_app (X : C) :
    (F.ofRawIsoComponentsInvGraded Gobj s e hnat).app X = eHomEquiv V (e X).inv :=
  F.ofRawIsoComponentsInvGraded_app Gobj s e hnat X

theorem raw_graded_hom_inv (X : C) :
    (λ_ (𝟙_ V)).inv ≫
        ((F.ofRawIsoComponentsGraded Gobj s e hnat).app X ⊗ₘ
          (F.ofRawIsoComponentsInvGraded Gobj s e hnat).app X) ≫
        eComp V (F.obj X) (Gobj X) (F.obj X) = eId V (F.obj X) := by
  rw [EnrichedFunctor.ofRawIsoComponentsGraded_app,
    EnrichedFunctor.ofRawIsoComponentsInvGraded_app]
  change (λ_ (𝟙_ V)).inv ≫
    (eHomEquiv V (e X).hom ⊗ₘ eHomEquiv V (e X).inv) ≫
      eComp V (F.obj X) (Gobj X) (F.obj X) = eId V (F.obj X)
  rw [← eHomEquiv_comp, (e X).hom_inv_id, eHomEquiv_id]

theorem raw_graded_inv_hom (X : C) :
    (λ_ (𝟙_ V)).inv ≫
        ((F.ofRawIsoComponentsInvGraded Gobj s e hnat).app X ⊗ₘ
          (F.ofRawIsoComponentsGraded Gobj s e hnat).app X) ≫
        eComp V (Gobj X) (F.obj X) (Gobj X) = eId V (Gobj X) := by
  rw [EnrichedFunctor.ofRawIsoComponentsInvGraded_app,
    EnrichedFunctor.ofRawIsoComponentsGraded_app]
  change (λ_ (𝟙_ V)).inv ≫
    (eHomEquiv V (e X).inv ⊗ₘ eHomEquiv V (e X).hom) ≫
      eComp V (Gobj X) (F.obj X) (Gobj X) = eId V (Gobj X)
  rw [← eHomEquiv_comp, (e X).inv_hom_id, eHomEquiv_id]

end Transport

end CategoryTheory.EnrichedMonoidalPublicClients
