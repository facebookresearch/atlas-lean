/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.InducedOrdinary
public import MathlibExt.CategoryTheory.Enriched.PointFunctionTransport
public import MathlibExt.CategoryTheory.Enriched.WholePointHomMap

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uC vC uD uH

open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalClosed

namespace WholeInducedPointFunctionTests

section OriginalData

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  (f : A → C)

example : (InducedCategory.enrichedOrdinaryCategory V f).toEnrichedCategory =
    EnrichedCategory.ofObjectFunction (V := V) f :=
  InducedCategory.enrichedOrdinaryCategory_enrichment V f

example (a b : A) : (EnrichedCategory.ofObjectFunction (V := V) f).Hom a b =
    (f a ⟶[V] f b) := EnrichedCategory.ofObjectFunction_hom f a b

example (a : A) : (EnrichedCategory.ofObjectFunction (V := V) f).id a = eId V (f a) :=
  EnrichedCategory.ofObjectFunction_id f a

example (a b c : A) : (EnrichedCategory.ofObjectFunction (V := V) f).comp a b c =
    eComp V (f a) (f b) (f c) := EnrichedCategory.ofObjectFunction_comp f a b c

example (a b : InducedCategory C f) (g : a ⟶ b) :
    (InducedCategory.enrichedOrdinaryCategory V f).homEquiv
      ((InducedCategory.enrichedOrdinaryCategory V f).homEquiv.symm
        (eHomEquiv V (C := C) (X := f a) (Y := f b) g.hom)) =
      eHomEquiv V (C := C) (X := f a) (Y := f b) g.hom :=
  (InducedCategory.enrichedOrdinaryCategory V f).homEquiv.apply_symm_apply _

example (a b : InducedCategory C f) (g : a ⟶ b) :
    (InducedCategory.enrichedOrdinaryCategory V f).homEquiv.symm
      ((InducedCategory.enrichedOrdinaryCategory V f).homEquiv g) = g :=
  (InducedCategory.enrichedOrdinaryCategory V f).homEquiv.symm_apply_apply _

example (a b : InducedCategory C f) :
    (InducedCategory.enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b) =
      (InducedCategory.homEquiv (F := f)).trans (eHomEquiv V) :=
  InducedCategory.enrichedOrdinaryCategory_homEquiv_function V f a b

example (a b : InducedCategory C f) :
    ((InducedCategory.enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b)).toFun =
      (fun g : a ⟶ b => eHomEquiv V g.hom) :=
  InducedCategory.enrichedOrdinaryCategory_point_function V f a b

example (a b : InducedCategory C f) :
    ((InducedCategory.enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b)).invFun =
      (fun p => InducedCategory.homMk (D := C) (F := f) (X := a) (Y := b)
        ((eHomEquiv V (C := C) (X := f a) (Y := f b)).symm p)) :=
  InducedCategory.enrichedOrdinaryCategory_inverse_function V f a b

end OriginalData

section OppositeData

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {A : Type uA} {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  (f : A → Cᵒᵖ)

example (a b : Cᵒᵖ) :
    (EnrichedOrdinaryCategory.opposite V).homEquiv (X := a) (Y := b) =
      Quiver.Hom.opEquiv.symm.trans (eHomEquiv V) :=
  EnrichedOrdinaryCategory.opposite_homEquiv_function V a b

example (a b : Cᵒᵖ) :
    ((EnrichedOrdinaryCategory.opposite V).homEquiv (X := a) (Y := b)).toFun =
      (fun g : a ⟶ b => eHomEquiv V g.unop) :=
  EnrichedOrdinaryCategory.opposite_point_function V a b

example (a b : Cᵒᵖ) :
    ((EnrichedOrdinaryCategory.opposite V).homEquiv (X := a) (Y := b)).invFun =
      (fun p => ((eHomEquiv V (C := C) (X := b.unop) (Y := a.unop)).symm p).op) :=
  EnrichedOrdinaryCategory.opposite_inverse_function V a b

example (a b : InducedCategory Cᵒᵖ f) :
    (InducedCategory.enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b) =
      (InducedCategory.homEquiv (F := f)).trans
        (Quiver.Hom.opEquiv.symm.trans (eHomEquiv V)) :=
  InducedCategory.enrichedOrdinaryCategory_opposite_homEquiv_function V f a b

example (a b : InducedCategory Cᵒᵖ f) :
    ((InducedCategory.enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b)).toFun =
      (fun g : a ⟶ b => eHomEquiv V g.hom.unop) :=
  InducedCategory.enrichedOrdinaryCategory_opposite_point_function V f a b

example (a b : InducedCategory Cᵒᵖ f) :
    ((InducedCategory.enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b)).invFun =
      (fun p => InducedCategory.homMk (D := Cᵒᵖ) (F := f) (X := a) (Y := b)
        (((eHomEquiv V (C := C) (X := (f b).unop) (Y := (f a).unop)).symm p).op)) :=
  InducedCategory.enrichedOrdinaryCategory_opposite_inverse_function V f a b

end OppositeData

section HomEndpointTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {X Y Z : V} {H : Sort uH} (h : X = Y)
  (p : H → (𝟙_ V ⟶ X)) (q : H → (𝟙_ V ⟶ Y)) (hp : HEq p q)

example : (fun f => p f ≫ eqToHom h) = q :=
  EnrichedPointFunctionTransport.point_function h p q hp

example (f : H) : p f ≫ eqToHom h = q f :=
  EnrichedPointFunctionTransport.point_function_apply h p q hp f

example : (fun f => p f ≫ (eqToIso h).hom) = q :=
  EnrichedPointFunctionTransport.point_function_eqToIso h p q hp

example (f : H) (r : Y ⟶ Z) : p f ≫ (eqToIso h).hom ≫ r = q f ≫ r :=
  EnrichedPointFunctionTransport.point_function_eqToIso_apply_assoc h p q hp f r

end HomEndpointTransport

section WholeHomMaps

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  (F : C ⥤ ForgetEnrichment V D)
  (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (F.obj X ⟶[V] F.obj Y))
  (hp : ∀ X Y : C,
    (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
      (fun f : X ⟶ Y => ForgetEnrichment.homTo V (F.map f)))

example (X : C) : eId V X ≫ m X X = eId V (F.obj X) :=
  UnitGeneratedEnrichment.map_id_of_point_function F m hp X

variable [MonoidalClosed V] (hsep : IsSeparator (𝟙_ V))

example (X Y Z : C) : eComp V X Y Z ≫ m X Z =
    (m X Y ⊗ₘ m Y Z) ≫ eComp V (F.obj X) (F.obj Y) (F.obj Z) :=
  UnitGeneratedEnrichment.map_comp_of_point_function F hsep m hp X Y Z

end WholeHomMaps

end WholeInducedPointFunctionTests
