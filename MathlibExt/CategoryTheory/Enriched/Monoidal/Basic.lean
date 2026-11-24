/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.NaturalTransformation
public import MathlibExt.CategoryTheory.Enriched.Ordinary.HomCongr
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
# Enriched monoidal category data

Named data for monoidal categories enriched over a braided base.  The
constructions in this file install no global enrichment or monoidal instances.

## Public imports

The natural-transformation conversion API, enriched hom congruence, and closed
self-enrichment are intentional public dependencies of this module.

## Public API

The main declarations are `EnrichedMonoidalCategoryData` and its tensor,
associator, and unitor operations; `EnrichedBraidedMonoidalCategoryData` and
its braiding; and `EnrichedSymmetricMonoidalCategoryData`.  The constraint
isomorphisms below expose complete, client-spellable endpoint functors.
`EnrichedFunctor.ofIsoComponents` and `EnrichedFunctor.ofRawIsoComponents`
transport full enriched functors through actual chosen value isomorphisms;
their isomorphisms and graded transformations retain both chosen component maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory.MonoidalCategory

universe uV vV uC vC uD vD uI vI uA vA uB vB uE vE uF vF

namespace CategoryTheory

namespace EnrichedFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
variable {D : Type uD} [Category.{vD} D] [EnrichedOrdinaryCategory V D]

private theorem map_eq_comp_eHomCongr
    {P Q R S : D} {H : V}
    (f : H ⟶ (P ⟶[V] Q)) (g : H ⟶ (R ⟶[V] S))
    (a : P ≅ R) (b : Q ≅ S)
    (h : f ≫ eHomWhiskerLeft V P b.hom =
      g ≫ eHomWhiskerRight V a.hom S) :
    g = f ≫ (Iso.eHomCongr V a b).hom := by
  apply (cancel_mono (Iso.eHomCongr V a b).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only [Iso.eHomCongr]
  rw [← Category.assoc]
  rw [← h]
  rw [Category.assoc, ← eHomWhiskerLeft_comp, b.hom_inv_id,
    eHomWhiskerLeft_id, Category.comp_id]

@[reassoc]
private theorem eComp_comp_eHomCongr
    {X Y Z X' Y' Z' : D}
    (a : X ≅ X') (b : Y ≅ Y') (c : Z ≅ Z') :
    eComp V X Y Z ≫ (Iso.eHomCongr V a c).hom =
      ((Iso.eHomCongr V a b).hom ⊗ₘ
          (Iso.eHomCongr V b c).hom) ≫
        eComp V X' Y' Z' := by
  simp only [Iso.eHomCongr, tensorHom_def, Category.assoc]
  rw [eComp_eHomWhiskerRight_assoc]
  rw [eComp_eHomWhiskerLeft]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [← eComp_eHomWhiskerLeft]
  rw [eHom_whisker_cancel_assoc]
  rw [eComp_eHomWhiskerLeft]

/-- Transport an enriched functor to chosen isomorphic values using the full Hom objects. -/
public def ofIsoComponents
    {C : Type uC} [EnrichedCategory V C]
    (F : EnrichedFunctor V C D) (Gobj : C → D)
    (e : ∀ X, F.obj X ≅ Gobj X) : EnrichedFunctor V C D where
  obj := Gobj
  map X Y := F.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom
  map_id X := by
    rw [F.map_id_assoc]
    exact Iso.eId_comp_eHomCongr V (e X)
  map_comp X Y Z := by
    rw [F.map_comp_assoc]
    rw [eComp_comp_eHomCongr]
    rw [← tensorHom_comp_tensorHom_assoc]

section Braided

variable [BraidedCategory V]

private theorem rawMap_eq_conjugateMap
    {C : Type uC} [EnrichedCategory V C]
    (F : EnrichedFunctor V C D) (Gobj : C → D)
    (s : ∀ X Y : C, (X ⟶[V] Y) ⟶ (Gobj X ⟶[V] Gobj Y))
    (e : ∀ X, F.obj X ≅ Gobj X)
    (hnat : ∀ X Y,
      (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
            (F.map X Y ⊗ₘ eHomEquiv V (e Y).hom) ≫
          eComp V (F.obj X) (F.obj Y) (Gobj Y) =
        (eHomEquiv V (e X).hom ⊗ₘ s X Y) ≫
          eComp V (F.obj X) (Gobj X) (Gobj Y))
    (X Y : C) :
    s X Y = F.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom := by
  apply map_eq_comp_eHomCongr (a := e X) (b := e Y)
  exact unitGradedNaturality_eq_whisker
    (F.map X Y) (s X Y) (e X).hom (e Y).hom (hnat X Y)

/-- Construct the enriched functor with the literal proposed Hom maps from their full
unit-graded naturality square with the chosen value isomorphisms. -/
public def ofRawIsoComponents
    {C : Type uC} [EnrichedCategory V C]
    (F : EnrichedFunctor V C D) (Gobj : C → D)
    (s : ∀ X Y : C, (X ⟶[V] Y) ⟶ (Gobj X ⟶[V] Gobj Y))
    (e : ∀ X, F.obj X ≅ Gobj X)
    (hnat : ∀ X Y,
      (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
            (F.map X Y ⊗ₘ eHomEquiv V (e Y).hom) ≫
          eComp V (F.obj X) (F.obj Y) (Gobj Y) =
        (eHomEquiv V (e X).hom ⊗ₘ s X Y) ≫
          eComp V (F.obj X) (Gobj X) (Gobj Y)) :
    EnrichedFunctor V C D where
  obj := Gobj
  map := s
  map_id X := by
    rw [rawMap_eq_conjugateMap F Gobj s e hnat]
    exact (ofIsoComponents F Gobj e).map_id X
  map_comp X Y Z := by
    rw [rawMap_eq_conjugateMap F Gobj s e hnat]
    rw [rawMap_eq_conjugateMap F Gobj s e hnat]
    rw [rawMap_eq_conjugateMap F Gobj s e hnat]
    exact (ofIsoComponents F Gobj e).map_comp X Y Z

end Braided

variable {C : Type uC} [EnrichedCategory V C]

section IsoComponents

variable (F : EnrichedFunctor V C D) (Gobj : C → D)
  (e : ∀ X, F.obj X ≅ Gobj X)

/-- The transported functor has exactly the chosen values. -/
@[simp]
public theorem ofIsoComponents_obj (X : C) :
    (F.ofIsoComponents Gobj e).obj X = Gobj X :=
  rfl

/-- The full transported Hom map uses the two actual endpoint isomorphisms. -/
@[simp]
public theorem ofIsoComponents_map (X Y : C) :
    (F.ofIsoComponents Gobj e).map X Y =
      F.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom :=
  rfl

/-- The inverse Hom-object isomorphism recovers the entire original Hom map. -/
@[reassoc]
public theorem ofIsoComponents_map_inv (X Y : C) :
    (F.ofIsoComponents Gobj e).map X Y ≫
        (Iso.eHomCongr V (e X) (e Y)).inv = F.map X Y := by
  change (F.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom) ≫
    (Iso.eHomCongr V (e X) (e Y)).inv = F.map X Y
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The chosen forward components are natural on the entire Hom objects. -/
@[reassoc]
public theorem ofIsoComponents_naturality (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft V (F.obj X) (e Y).hom =
      (F.ofIsoComponents Gobj e).map X Y ≫
        eHomWhiskerRight V (e X).hom (Gobj Y) := by
  change F.map X Y ≫ eHomWhiskerLeft V (F.obj X) (e Y).hom =
    (F.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom) ≫
      eHomWhiskerRight V (e X).hom (Gobj Y)
  simp only [Iso.eHomCongr, Category.assoc]
  rw [eHom_whisker_exchange, ← eHomWhiskerRight_comp_assoc,
    (e X).hom_inv_id, eHomWhiskerRight_id, Category.id_comp]

/-- The chosen inverse components are natural on the entire Hom objects. -/
@[reassoc]
public theorem ofIsoComponents_inv_naturality (X Y : C) :
    (F.ofIsoComponents Gobj e).map X Y ≫
        eHomWhiskerLeft V (Gobj X) (e Y).inv =
      F.map X Y ≫ eHomWhiskerRight V (e X).inv (F.obj Y) := by
  change (F.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom) ≫
      eHomWhiskerLeft V (Gobj X) (e Y).inv =
    F.map X Y ≫ eHomWhiskerRight V (e X).inv (F.obj Y)
  simp only [Iso.eHomCongr, Category.assoc]
  rw [← eHomWhiskerLeft_comp, (e Y).hom_inv_id,
    eHomWhiskerLeft_id, Category.comp_id]

private def isoOfWhiskerComponents {F G : EnrichedFunctor V C D}
    (e : ∀ X, F.obj X ≅ G.obj X)
    (h : ∀ X Y,
      F.map X Y ≫ eHomWhiskerLeft V (F.obj X) (e Y).hom =
        G.map X Y ≫ eHomWhiskerRight V (e X).hom (G.obj Y)) : F ≅ G :=
  EnrichedFunctor.isoMk <| NatIso.ofComponents
    (fun X => (ForgetEnrichment.equiv (D := D) V).inverse.mapIso
      (e (ForgetEnrichment.to V X))) (by
        intro X Y f
        have hp :
            (eHomEquiv V).symm (ForgetEnrichment.homTo V f ≫
                F.map (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y)) ≫
              (e (ForgetEnrichment.to V Y)).hom =
            (e (ForgetEnrichment.to V X)).hom ≫
              (eHomEquiv V).symm (ForgetEnrichment.homTo V f ≫
                G.map (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y)) := by
          apply (eHomEquiv V).injective
          rw [← eHomEquiv_comp_eHomWhiskerLeft,
            ← eHomEquiv_comp_eHomWhiskerRight]
          simp only [Equiv.apply_symm_apply]
          simpa only [Category.assoc] using congrArg
            (fun k => ForgetEnrichment.homTo V f ≫ k)
            (h (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y))
        change
          ForgetEnrichment.homOf V (ForgetEnrichment.homTo V f ≫
              F.map (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y)) ≫
            ForgetEnrichment.homOf V (eHomEquiv V
              (e (ForgetEnrichment.to V Y)).hom) =
          ForgetEnrichment.homOf V (eHomEquiv V
              (e (ForgetEnrichment.to V X)).hom) ≫
            ForgetEnrichment.homOf V (ForgetEnrichment.homTo V f ≫
              G.map (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y))
        have hp' := congrArg
          (fun k => (ForgetEnrichment.equivInverse V D).map k) hp
        dsimp only [ForgetEnrichment.equivInverse] at hp'
        simpa only [eHomEquiv_comp, Equiv.apply_symm_apply,
          ForgetEnrichment.homOf_comp] using hp')

/-- The chosen value isomorphisms give an isomorphism of the full enriched functors. -/
@[no_expose] public def ofIsoComponentsIso : F ≅ F.ofIsoComponents Gobj e :=
  isoOfWhiskerComponents e (fun X Y => F.ofIsoComponents_naturality Gobj e X Y)

private theorem ofIsoComponentsIso_hom_app_private (X : C) :
    (F.ofIsoComponentsIso Gobj e).hom.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).hom) :=
  rfl

/-- The forward natural transformation retains the chosen forward component. -/
@[simp]
public theorem ofIsoComponentsIso_hom_app (X : C) :
    (F.ofIsoComponentsIso Gobj e).hom.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).hom) :=
  ofIsoComponentsIso_hom_app_private F Gobj e X

private theorem ofIsoComponentsIso_inv_app_private (X : C) :
    (F.ofIsoComponentsIso Gobj e).inv.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).inv) :=
  rfl

/-- The inverse natural transformation retains the chosen inverse component. -/
@[simp]
public theorem ofIsoComponentsIso_inv_app (X : C) :
    (F.ofIsoComponentsIso Gobj e).inv.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).inv) :=
  ofIsoComponentsIso_inv_app_private F Gobj e X

private theorem ofIsoComponentsIso_hom_component_private (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofIsoComponentsIso Gobj e).hom.out.app (ForgetEnrichment.of V X))) =
        (e X).hom :=
  (eHomEquiv V).symm_apply_apply _

/-- The forward component, read as an actual arrow of the target, is the chosen arrow. -/
public theorem ofIsoComponentsIso_hom_component (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofIsoComponentsIso Gobj e).hom.out.app (ForgetEnrichment.of V X))) =
        (e X).hom :=
  ofIsoComponentsIso_hom_component_private F Gobj e X

private theorem ofIsoComponentsIso_inv_component_private (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofIsoComponentsIso Gobj e).inv.out.app (ForgetEnrichment.of V X))) =
        (e X).inv :=
  (eHomEquiv V).symm_apply_apply _

/-- The inverse component, read as an actual arrow of the target, is the chosen arrow. -/
public theorem ofIsoComponentsIso_inv_component (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofIsoComponentsIso Gobj e).inv.out.app (ForgetEnrichment.of V X))) =
        (e X).inv :=
  ofIsoComponentsIso_inv_component_private F Gobj e X

end IsoComponents

section BraidedComponents

variable [BraidedCategory V]

private def gradedOfWhiskerComponents {F G : EnrichedFunctor V C D}
    (q : ∀ X, F.obj X ⟶ G.obj X)
    (hq : ∀ X Y,
      F.map X Y ≫ eHomWhiskerLeft V (F.obj X) (q Y) =
        G.map X Y ≫ eHomWhiskerRight V (q X) (G.obj Y)) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G where
  app X := eHomEquiv V (q X)
  naturality X Y := by
    dsimp only [Center.ofBraided, Center.ofBraidedObj]
    apply (cancel_epi (λ_ (X ⟶[V] Y)).inv).1
    rw [leftUnitor_inv_braiding_assoc]
    have h := hq X Y
    dsimp only [eHomWhiskerLeft, eHomWhiskerRight] at h
    rw [rightUnitor_inv_naturality_assoc, leftUnitor_inv_naturality_assoc] at h
    rw [← tensorHom_id, ← id_tensorHom, whisker_exchange_assoc,
      ← tensorHom_def_assoc] at h
    simpa only [Category.assoc, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.id_comp] using h

section IsoComponents

variable (F : EnrichedFunctor V C D) (Gobj : C → D)
  (e : ∀ X, F.obj X ≅ Gobj X)

/-- The chosen forward components satisfy the genuine unit-graded Hom-object square. -/
@[no_expose] public def ofIsoComponentsGraded :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F
      (F.ofIsoComponents Gobj e) :=
  gradedOfWhiskerComponents (fun X => (e X).hom)
    (fun X Y => F.ofIsoComponents_naturality Gobj e X Y)

private theorem ofIsoComponentsGraded_app_private (X : C) :
    (F.ofIsoComponentsGraded Gobj e).app X = eHomEquiv V (e X).hom :=
  rfl

/-- The forward unit-graded component is the actual chosen forward arrow. -/
@[simp]
public theorem ofIsoComponentsGraded_app (X : C) :
    (F.ofIsoComponentsGraded Gobj e).app X = eHomEquiv V (e X).hom :=
  ofIsoComponentsGraded_app_private F Gobj e X

/-- The chosen inverse components satisfy the genuine unit-graded Hom-object square. -/
@[no_expose] public def ofIsoComponentsInvGraded :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (F.ofIsoComponents Gobj e) F :=
  gradedOfWhiskerComponents (fun X => (e X).inv)
    (fun X Y => F.ofIsoComponents_inv_naturality Gobj e X Y)

private theorem ofIsoComponentsInvGraded_app_private (X : C) :
    (F.ofIsoComponentsInvGraded Gobj e).app X = eHomEquiv V (e X).inv :=
  rfl

/-- The inverse unit-graded component is the actual chosen inverse arrow. -/
@[simp]
public theorem ofIsoComponentsInvGraded_app (X : C) :
    (F.ofIsoComponentsInvGraded Gobj e).app X = eHomEquiv V (e X).inv :=
  ofIsoComponentsInvGraded_app_private F Gobj e X

private theorem ofIsoComponentsGraded_comp_inv_private (X : C) :
    (λ_ (𝟙_ V)).inv ≫
          ((F.ofIsoComponentsGraded Gobj e).app X ⊗ₘ
            (F.ofIsoComponentsInvGraded Gobj e).app X) ≫
        eComp V (F.obj X) (Gobj X) (F.obj X) = eId V (F.obj X) := by
  change (λ_ (𝟙_ V)).inv ≫
      (eHomEquiv V (e X).hom ⊗ₘ eHomEquiv V (e X).inv) ≫
      eComp V (F.obj X) (Gobj X) (F.obj X) = eId V (F.obj X)
  rw [← eHomEquiv_comp, (e X).hom_inv_id, eHomEquiv_id]

/-- Source-first composition of the forward and inverse graded components is identity. -/
public theorem ofIsoComponentsGraded_comp_inv (X : C) :
    (λ_ (𝟙_ V)).inv ≫
          ((F.ofIsoComponentsGraded Gobj e).app X ⊗ₘ
            (F.ofIsoComponentsInvGraded Gobj e).app X) ≫
        eComp V (F.obj X) (Gobj X) (F.obj X) = eId V (F.obj X) :=
  ofIsoComponentsGraded_comp_inv_private F Gobj e X

private theorem ofIsoComponentsInvGraded_comp_hom_private (X : C) :
    (λ_ (𝟙_ V)).inv ≫
          ((F.ofIsoComponentsInvGraded Gobj e).app X ⊗ₘ
            (F.ofIsoComponentsGraded Gobj e).app X) ≫
        eComp V (Gobj X) (F.obj X) (Gobj X) = eId V (Gobj X) := by
  change (λ_ (𝟙_ V)).inv ≫
      (eHomEquiv V (e X).inv ⊗ₘ eHomEquiv V (e X).hom) ≫
      eComp V (Gobj X) (F.obj X) (Gobj X) = eId V (Gobj X)
  rw [← eHomEquiv_comp, (e X).inv_hom_id, eHomEquiv_id]

/-- Source-first composition in the opposite order is the chosen value's identity. -/
public theorem ofIsoComponentsInvGraded_comp_hom (X : C) :
    (λ_ (𝟙_ V)).inv ≫
          ((F.ofIsoComponentsInvGraded Gobj e).app X ⊗ₘ
            (F.ofIsoComponentsGraded Gobj e).app X) ≫
        eComp V (Gobj X) (F.obj X) (Gobj X) = eId V (Gobj X) :=
  ofIsoComponentsInvGraded_comp_hom_private F Gobj e X

end IsoComponents

section RawIsoComponents

variable (F : EnrichedFunctor V C D) (Gobj : C → D)
  (s : ∀ X Y : C, (X ⟶[V] Y) ⟶ (Gobj X ⟶[V] Gobj Y))
  (e : ∀ X, F.obj X ≅ Gobj X)
  (hnat : ∀ X Y,
    (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
          (F.map X Y ⊗ₘ eHomEquiv V (e Y).hom) ≫
        eComp V (F.obj X) (F.obj Y) (Gobj Y) =
      (eHomEquiv V (e X).hom ⊗ₘ s X Y) ≫
        eComp V (F.obj X) (Gobj X) (Gobj Y))

/-- The raw construction has exactly the chosen values. -/
@[simp]
public theorem ofRawIsoComponents_obj (X : C) :
    (F.ofRawIsoComponents Gobj s e hnat).obj X = Gobj X :=
  rfl

/-- The raw construction keeps exactly the original proposed Hom maps. -/
@[simp]
public theorem ofRawIsoComponents_map (X Y : C) :
    (F.ofRawIsoComponents Gobj s e hnat).map X Y = s X Y :=
  rfl

/-- The full original naturality square determines each entire raw Hom map. -/
public theorem ofRawIsoComponents_map_eq (X Y : C) :
    (F.ofRawIsoComponents Gobj s e hnat).map X Y =
      F.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom :=
  rawMap_eq_conjugateMap F Gobj s e hnat X Y

/-- The actual inverse Hom-object map recovers the whole original action. -/
@[reassoc]
public theorem ofRawIsoComponents_map_inv (X Y : C) :
    (F.ofRawIsoComponents Gobj s e hnat).map X Y ≫
        (Iso.eHomCongr V (e X) (e Y)).inv = F.map X Y := by
  change s X Y ≫ (Iso.eHomCongr V (e X) (e Y)).inv = F.map X Y
  rw [rawMap_eq_conjugateMap F Gobj s e hnat,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The raw functor's chosen forward arrows are natural on the entire Hom objects. -/
@[reassoc]
public theorem ofRawIsoComponents_naturality (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft V (F.obj X) (e Y).hom =
      (F.ofRawIsoComponents Gobj s e hnat).map X Y ≫
        eHomWhiskerRight V (e X).hom (Gobj Y) := by
  change F.map X Y ≫ eHomWhiskerLeft V (F.obj X) (e Y).hom =
    s X Y ≫ eHomWhiskerRight V (e X).hom (Gobj Y)
  exact unitGradedNaturality_eq_whisker
    (F.map X Y) (s X Y) (e X).hom (e Y).hom (hnat X Y)

/-- The actual chosen inverse arrows are natural for the literal raw Hom maps. -/
@[reassoc]
public theorem ofRawIsoComponents_inv_naturality (X Y : C) :
    (F.ofRawIsoComponents Gobj s e hnat).map X Y ≫
        eHomWhiskerLeft V (Gobj X) (e Y).inv =
      F.map X Y ≫ eHomWhiskerRight V (e X).inv (F.obj Y) := by
  change s X Y ≫ eHomWhiskerLeft V (Gobj X) (e Y).inv =
    F.map X Y ≫ eHomWhiskerRight V (e X).inv (F.obj Y)
  rw [rawMap_eq_conjugateMap F Gobj s e hnat]
  exact F.ofIsoComponents_inv_naturality Gobj e X Y

/-- The literal raw enriched functor is isomorphic to the original functor via the chosen arrows. -/
@[no_expose] public def ofRawIsoComponentsIso :
    F ≅ F.ofRawIsoComponents Gobj s e hnat :=
  isoOfWhiskerComponents e
    (fun X Y => F.ofRawIsoComponents_naturality Gobj s e hnat X Y)

private theorem ofRawIsoComponentsIso_hom_app_private (X : C) :
    (F.ofRawIsoComponentsIso Gobj s e hnat).hom.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).hom) :=
  rfl

/-- The raw functor isomorphism retains the chosen forward component. -/
@[simp]
public theorem ofRawIsoComponentsIso_hom_app (X : C) :
    (F.ofRawIsoComponentsIso Gobj s e hnat).hom.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).hom) :=
  ofRawIsoComponentsIso_hom_app_private F Gobj s e hnat X

private theorem ofRawIsoComponentsIso_inv_app_private (X : C) :
    (F.ofRawIsoComponentsIso Gobj s e hnat).inv.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).inv) :=
  rfl

/-- The raw functor isomorphism retains the chosen inverse component. -/
@[simp]
public theorem ofRawIsoComponentsIso_inv_app (X : C) :
    (F.ofRawIsoComponentsIso Gobj s e hnat).inv.out.app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (eHomEquiv V (e X).inv) :=
  ofRawIsoComponentsIso_inv_app_private F Gobj s e hnat X

private theorem ofRawIsoComponentsIso_hom_component_private (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofRawIsoComponentsIso Gobj s e hnat).hom.out.app (ForgetEnrichment.of V X))) =
        (e X).hom :=
  (eHomEquiv V).symm_apply_apply _

/-- The raw functor's forward isomorphism component is the actual target arrow. -/
public theorem ofRawIsoComponentsIso_hom_component (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofRawIsoComponentsIso Gobj s e hnat).hom.out.app (ForgetEnrichment.of V X))) =
        (e X).hom :=
  ofRawIsoComponentsIso_hom_component_private F Gobj s e hnat X

private theorem ofRawIsoComponentsIso_inv_component_private (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofRawIsoComponentsIso Gobj s e hnat).inv.out.app (ForgetEnrichment.of V X))) =
        (e X).inv :=
  (eHomEquiv V).symm_apply_apply _

/-- The raw functor's inverse isomorphism component is the actual target arrow. -/
public theorem ofRawIsoComponentsIso_inv_component (X : C) :
    (eHomEquiv V).symm (ForgetEnrichment.homTo V
      ((F.ofRawIsoComponentsIso Gobj s e hnat).inv.out.app (ForgetEnrichment.of V X))) =
        (e X).inv :=
  ofRawIsoComponentsIso_inv_component_private F Gobj s e hnat X

/-- The original full unit-graded square is retained by the raw functor construction. -/
@[no_expose] public def ofRawIsoComponentsGraded :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F
      (F.ofRawIsoComponents Gobj s e hnat) where
  app X := eHomEquiv V (e X).hom
  naturality X Y := by
    dsimp only [Center.ofBraided, Center.ofBraidedObj]
    exact hnat X Y

private theorem ofRawIsoComponentsGraded_app_private (X : C) :
    (F.ofRawIsoComponentsGraded Gobj s e hnat).app X = eHomEquiv V (e X).hom :=
  rfl

/-- The raw functor's forward graded component is exactly the chosen arrow. -/
@[simp]
public theorem ofRawIsoComponentsGraded_app (X : C) :
    (F.ofRawIsoComponentsGraded Gobj s e hnat).app X = eHomEquiv V (e X).hom :=
  ofRawIsoComponentsGraded_app_private F Gobj s e hnat X

/-- The literal raw Hom maps admit the actual chosen inverse graded transformation. -/
@[no_expose] public def ofRawIsoComponentsInvGraded :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (F.ofRawIsoComponents Gobj s e hnat) F :=
  gradedOfWhiskerComponents (fun X => (e X).inv)
    (fun X Y => F.ofRawIsoComponents_inv_naturality Gobj s e hnat X Y)

private theorem ofRawIsoComponentsInvGraded_app_private (X : C) :
    (F.ofRawIsoComponentsInvGraded Gobj s e hnat).app X = eHomEquiv V (e X).inv :=
  rfl

/-- The raw functor's inverse graded component is exactly the chosen inverse arrow. -/
@[simp]
public theorem ofRawIsoComponentsInvGraded_app (X : C) :
    (F.ofRawIsoComponentsInvGraded Gobj s e hnat).app X = eHomEquiv V (e X).inv :=
  ofRawIsoComponentsInvGraded_app_private F Gobj s e hnat X

end RawIsoComponents

end BraidedComponents

end EnrichedFunctor

namespace Enriched

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable (C : Type uC) [EnrichedCategory V C]
variable (D : Type uD) [EnrichedCategory V D]

/-- The product of two `V`-enriched categories, using the braided
interchange on hom objects. -/
@[instance_reducible]
public def prodCategory : EnrichedCategory V (C × D) := by
  letI : EnrichedCategory (V × V) (C × D) :=
    { Hom := fun X Y => (X.1 ⟶[V] Y.1, X.2 ⟶[V] Y.2)
      id := fun X => (eId V X.1, eId V X.2)
      comp := fun X Y Z =>
        (eComp V X.1 Y.1 Z.1, eComp V X.2 Y.2 Z.2)
      id_comp := fun X Y => by ext <;> simp
      comp_id := fun X Y => by ext <;> simp
      assoc := fun W X Y Z => by ext <;> simp }
  let transported : EnrichedCategory V (C × D) :=
    inferInstanceAs
      (EnrichedCategory V
        (TransportEnrichment (MonoidalCategory.tensor V) (C × D)))
  exact
    { Hom := fun X Y => (X.1 ⟶[V] Y.1) ⊗ (X.2 ⟶[V] Y.2)
      id := fun X => (λ_ (𝟙_ V)).inv ≫ (eId V X.1 ⊗ₘ eId V X.2)
      comp := fun X Y Z =>
        MonoidalCategory.tensorμ
            (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)
            (Y.1 ⟶[V] Z.1) (Y.2 ⟶[V] Z.2) ≫
          (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2)
      id_comp := transported.id_comp
      comp_id := transported.comp_id
      assoc := transported.assoc }

/-- The identity of the product enrichment. -/
public theorem prodEId (X : C × D) :
    (prodCategory V C D).id X =
      (λ_ (𝟙_ V)).inv ≫ (eId V X.1 ⊗ₘ eId V X.2) :=
  rfl

/-- Composition in the product enrichment is componentwise composition
after the middle-braiding interchange. -/
public theorem prodEComp (X Y Z : C × D) :
    (prodCategory V C D).comp X Y Z =
      MonoidalCategory.tensorμ
          (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)
          (Y.1 ⟶[V] Z.1) (Y.2 ⟶[V] Z.2) ≫
        (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2) :=
  rfl

end Enriched

attribute [local instance] Enriched.prodCategory

/-- The product of two enriched functors on their original product-enriched Hom objects. -/
public def prodEnrichedFunctor
    {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
    [BraidedCategory V]
    {A : Type uA} [EnrichedCategory V A]
    {B : Type uB} [EnrichedCategory V B]
    {E : Type uE} [EnrichedCategory V E]
    {F : Type uF} [EnrichedCategory V F]
    (L : EnrichedFunctor V A B) (R : EnrichedFunctor V E F) :
    EnrichedFunctor V (A × E) (B × F) where
  obj X := (L.obj X.1, R.obj X.2)
  map X Y := L.map X.1 Y.1 ⊗ₘ R.map X.2 Y.2
  map_id X := by
    change ((λ_ (𝟙_ V)).inv ≫
          (eId V X.1 ⊗ₘ eId V X.2)) ≫
        (L.map X.1 X.1 ⊗ₘ R.map X.2 X.2) =
      (λ_ (𝟙_ V)).inv ≫
        (eId V (L.obj X.1) ⊗ₘ eId V (R.obj X.2))
    rw [Category.assoc, tensorHom_comp_tensorHom, L.map_id, R.map_id]
  map_comp X Y Z := by
    change (MonoidalCategory.tensorμ
          (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)
          (Y.1 ⟶[V] Z.1) (Y.2 ⟶[V] Z.2) ≫
        (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2)) ≫
          (L.map X.1 Z.1 ⊗ₘ R.map X.2 Z.2) =
      ((L.map X.1 Y.1 ⊗ₘ R.map X.2 Y.2) ⊗ₘ
          (L.map Y.1 Z.1 ⊗ₘ R.map Y.2 Z.2)) ≫
        MonoidalCategory.tensorμ
          (L.obj X.1 ⟶[V] L.obj Y.1)
          (R.obj X.2 ⟶[V] R.obj Y.2)
          (L.obj Y.1 ⟶[V] L.obj Z.1)
          (R.obj Y.2 ⟶[V] R.obj Z.2) ≫
        (eComp V (L.obj X.1) (L.obj Y.1) (L.obj Z.1) ⊗ₘ
          eComp V (R.obj X.2) (R.obj Y.2) (R.obj Z.2))
    rw [Category.assoc, tensorHom_comp_tensorHom, L.map_comp, R.map_comp]
    rw [← tensorHom_comp_tensorHom]
    rw [MonoidalCategory.tensorμ_natural_assoc]

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable (I : Type uI) [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- The hom-object data making the selected ordinary monoidal structure on
`I` enriched over `V`.  Naturality of all ordinary constraints is stored as
genuine unit-graded hom-object equations. -/
public structure EnrichedMonoidalCategoryData where
  /-- Tensoring two hom objects. -/
  tensorMap : ∀ i i' j j' : I,
    ((i ⟶[V] i') ⊗ (j ⟶[V] j')) ⟶
      ((i ⊗ j) ⟶[V] (i' ⊗ j'))
  /-- Tensoring commutes with enriched composition. -/
  tensorMap_comp : ∀ i i' i'' j j' j'' : I,
    (Enriched.prodCategory V I I).comp
          (i, j) (i', j') (i'', j'') ≫
        tensorMap i i'' j j'' =
      (tensorMap i i' j j' ⊗ₘ tensorMap i' i'' j' j'') ≫
        eComp V (i ⊗ j) (i' ⊗ j') (i'' ⊗ j'')
  /-- The hom-object tensor refines the selected ordinary tensor on arrows. -/
  tensorMap_eHomEquiv : ∀ {i i' j j' : I}
      (f : i ⟶ i') (g : j ⟶ j'),
    (λ_ (𝟙_ V)).inv ≫
          (eHomEquiv V f ⊗ₘ eHomEquiv V g) ≫
        tensorMap i i' j j' =
      eHomEquiv V (f ⊗ₘ g)
  /-- Genuine hom-object naturality of the associator. -/
  associatorNaturality : ∀ i i' j j' k k' : I,
    (β_ (𝟙_ V)
          (((i ⟶[V] i') ⊗ (j ⟶[V] j')) ⊗ (k ⟶[V] k'))).hom ≫
          (((tensorMap i i' j j' ▷ (k ⟶[V] k')) ≫
              tensorMap (i ⊗ j) (i' ⊗ j') k k') ⊗ₘ
            eHomEquiv V (α_ i' j' k').hom) ≫
        eComp V ((i ⊗ j) ⊗ k) ((i' ⊗ j') ⊗ k')
          (i' ⊗ (j' ⊗ k')) =
      (eHomEquiv V (α_ i j k).hom ⊗ₘ
          ((α_ (i ⟶[V] i') (j ⟶[V] j') (k ⟶[V] k')).hom ≫
            ((i ⟶[V] i') ◁ tensorMap j j' k k') ≫
            tensorMap i i' (j ⊗ k) (j' ⊗ k'))) ≫
        eComp V ((i ⊗ j) ⊗ k) (i ⊗ (j ⊗ k))
          (i' ⊗ (j' ⊗ k'))
  /-- Genuine hom-object naturality of the left unitor. -/
  leftUnitorNaturality : ∀ i i' : I,
    (β_ (𝟙_ V) (i ⟶[V] i')).hom ≫
          (((λ_ (i ⟶[V] i')).inv ≫
                (eId V (𝟙_ I) ⊗ₘ 𝟙 (i ⟶[V] i')) ≫
              tensorMap (𝟙_ I) (𝟙_ I) i i') ⊗ₘ
            eHomEquiv V (λ_ i').hom) ≫
        eComp V (𝟙_ I ⊗ i) (𝟙_ I ⊗ i') i' =
      (eHomEquiv V (λ_ i).hom ⊗ₘ 𝟙 (i ⟶[V] i')) ≫
        eComp V (𝟙_ I ⊗ i) i i'
  /-- Genuine hom-object naturality of the right unitor. -/
  rightUnitorNaturality : ∀ i i' : I,
    (β_ (𝟙_ V) (i ⟶[V] i')).hom ≫
          (((ρ_ (i ⟶[V] i')).inv ≫
                (𝟙 (i ⟶[V] i') ⊗ₘ eId V (𝟙_ I)) ≫
              tensorMap i i' (𝟙_ I) (𝟙_ I)) ⊗ₘ
            eHomEquiv V (ρ_ i').hom) ≫
        eComp V (i ⊗ 𝟙_ I) (i' ⊗ 𝟙_ I) i' =
      (eHomEquiv V (ρ_ i).hom ⊗ₘ 𝟙 (i ⟶[V] i')) ≫
        eComp V (i ⊗ 𝟙_ I) i i'

namespace EnrichedMonoidalCategoryData

variable {V I}

omit [BraidedCategory V] [MonoidalCategory I] in
private theorem eId_tensor_eId_comp (i : I) :
    (eId V i ⊗ₘ eId V i) ≫ eComp V i i i =
      (λ_ (𝟙_ V)).hom ≫ eId V i := by
  rw [← cancel_epi (λ_ (𝟙_ V)).inv]
  simp only [Iso.inv_hom_id_assoc]
  rw [leftUnitor_inv_comp_tensorHom_assoc]
  rw [e_id_comp, Category.comp_id]

omit [BraidedCategory V] [Category I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] in
private theorem tensorHom_eq_leftUnitor_hom_comp
    {X Y Z : V} (f : 𝟙_ V ⟶ Y) (g : X ⟶ Z) :
    f ⊗ₘ g =
      (λ_ X).hom ≫ g ≫ (λ_ Z).inv ≫ f ▷ Z := by
  rw [← cancel_epi (λ_ X).inv]
  simp only [Iso.inv_hom_id_assoc]
  exact leftUnitor_inv_comp_tensorHom f g

omit [BraidedCategory V] [Category I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] in
private theorem tensorHom_eq_rightUnitor_hom_comp
    {X Y Z : V} (f : X ⟶ Y) (g : 𝟙_ V ⟶ Z) :
    f ⊗ₘ g =
      (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv ≫ Y ◁ g := by
  rw [← cancel_epi (ρ_ X).inv]
  simp only [Iso.inv_hom_id_assoc]
  exact rightUnitor_inv_comp_tensorHom f g

/-- Tensoring identities gives the enriched identity. -/
public theorem tensorMap_id (d : EnrichedMonoidalCategoryData V I) (i j : I) :
    (Enriched.prodCategory V I I).id (i, j) ≫
        d.tensorMap i i j j =
      eId V (i ⊗ j) := by
  rw [Enriched.prodEId]
  rw [Category.assoc]
  simpa only [eHomEquiv_id, MonoidalCategory.id_tensorHom_id] using
    d.tensorMap_eHomEquiv (𝟙 i) (𝟙 j)

/-- The selected tensor is an enriched functor from the product enrichment. -/
public def tensorEnrichedFunctor (d : EnrichedMonoidalCategoryData V I) :
    EnrichedFunctor V (I × I) I where
  obj X := X.1 ⊗ X.2
  map X Y := d.tensorMap X.1 Y.1 X.2 Y.2
  map_id X := d.tensorMap_id X.1 X.2
  map_comp X Y Z := d.tensorMap_comp
    X.1 Y.1 Z.1 X.2 Y.2 Z.2

private def associatorLeftFunctor
    (d : EnrichedMonoidalCategoryData V I) :
    EnrichedFunctor V ((I × I) × I) I :=
  (prodEnrichedFunctor d.tensorEnrichedFunctor
      (EnrichedFunctor.id V I)).comp V d.tensorEnrichedFunctor

private def associatorRightFunctor
    (d : EnrichedMonoidalCategoryData V I) :
    EnrichedFunctor V ((I × I) × I) I where
  obj X := X.1.1 ⊗ (X.1.2 ⊗ X.2)
  map X Y :=
    (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2)
        (X.2 ⟶[V] Y.2)).hom ≫
      ((X.1.1 ⟶[V] Y.1.1) ◁
        d.tensorMap X.1.2 Y.1.2 X.2 Y.2) ≫
      d.tensorMap X.1.1 Y.1.1
        (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2)
  map_id X := by
    change ((λ_ (𝟙_ V)).inv ≫
          (((λ_ (𝟙_ V)).inv ≫
              (eId V X.1.1 ⊗ₘ eId V X.1.2)) ⊗ₘ eId V X.2)) ≫
        (α_ (X.1.1 ⟶[V] X.1.1) (X.1.2 ⟶[V] X.1.2)
          (X.2 ⟶[V] X.2)).hom ≫
        ((X.1.1 ⟶[V] X.1.1) ◁
          d.tensorMap X.1.2 X.1.2 X.2 X.2) ≫
        d.tensorMap X.1.1 X.1.1
          (X.1.2 ⊗ X.2) (X.1.2 ⊗ X.2) =
      eId V (X.1.1 ⊗ (X.1.2 ⊗ X.2))
    rw [← d.tensorMap_id X.1.1 (X.1.2 ⊗ X.2)]
    rw [Enriched.prodEId]
    rw [← d.tensorMap_id X.1.2 X.2]
    rw [Enriched.prodEId]
    monoidal
  map_comp X Y Z := by
    change (MonoidalCategory.tensorμ
          ((X.1.1 ⟶[V] Y.1.1) ⊗ (X.1.2 ⟶[V] Y.1.2))
          (X.2 ⟶[V] Y.2)
          ((Y.1.1 ⟶[V] Z.1.1) ⊗ (Y.1.2 ⟶[V] Z.1.2))
          (Y.2 ⟶[V] Z.2) ≫
        ((MonoidalCategory.tensorμ
              (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2)
              (Y.1.1 ⟶[V] Z.1.1) (Y.1.2 ⟶[V] Z.1.2) ≫
            (eComp V X.1.1 Y.1.1 Z.1.1 ⊗ₘ
              eComp V X.1.2 Y.1.2 Z.1.2)) ⊗ₘ
          eComp V X.2 Y.2 Z.2)) ≫
        (α_ (X.1.1 ⟶[V] Z.1.1) (X.1.2 ⟶[V] Z.1.2)
          (X.2 ⟶[V] Z.2)).hom ≫
        ((X.1.1 ⟶[V] Z.1.1) ◁
          d.tensorMap X.1.2 Z.1.2 X.2 Z.2) ≫
        d.tensorMap X.1.1 Z.1.1
          (X.1.2 ⊗ X.2) (Z.1.2 ⊗ Z.2) =
      (((α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2)
              (X.2 ⟶[V] Y.2)).hom ≫
            ((X.1.1 ⟶[V] Y.1.1) ◁
              d.tensorMap X.1.2 Y.1.2 X.2 Y.2) ≫
            d.tensorMap X.1.1 Y.1.1
              (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2)) ⊗ₘ
          ((α_ (Y.1.1 ⟶[V] Z.1.1) (Y.1.2 ⟶[V] Z.1.2)
              (Y.2 ⟶[V] Z.2)).hom ≫
            ((Y.1.1 ⟶[V] Z.1.1) ◁
              d.tensorMap Y.1.2 Z.1.2 Y.2 Z.2) ≫
            d.tensorMap Y.1.1 Z.1.1
              (Y.1.2 ⊗ Y.2) (Z.1.2 ⊗ Z.2))) ≫
        eComp V (X.1.1 ⊗ (X.1.2 ⊗ X.2))
          (Y.1.1 ⊗ (Y.1.2 ⊗ Y.2))
          (Z.1.1 ⊗ (Z.1.2 ⊗ Z.2))
    rw [← tensorHom_comp_tensorHom_assoc]
    rw [← tensorHom_comp_tensorHom_assoc]
    rw [← d.tensorMap_comp X.1.1 Y.1.1 Z.1.1
      (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2) (Z.1.2 ⊗ Z.2)]
    rw [Enriched.prodEComp]
    simp only [Category.assoc, ← id_tensorHom]
    rw [MonoidalCategory.tensorμ_natural_assoc
      (𝟙 (X.1.1 ⟶[V] Y.1.1))
      (d.tensorMap X.1.2 Y.1.2 X.2 Y.2)
      (𝟙 (Y.1.1 ⟶[V] Z.1.1))
      (d.tensorMap Y.1.2 Z.1.2 Y.2 Z.2)]
    rw [tensorHom_comp_tensorHom_assoc]
    rw [← d.tensorMap_comp X.1.2 Y.1.2 Z.1.2 X.2 Y.2 Z.2]
    simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    nth_rewrite 2 [← Category.comp_id (eComp V X.1.1 Y.1.1 Z.1.1)]
    rw [← tensorHom_comp_tensorHom_assoc]
    rw [Enriched.prodEComp]
    nth_rewrite 2 [← Category.id_comp (eComp V X.1.1 Y.1.1 Z.1.1)]
    rw [← tensorHom_comp_tensorHom_assoc]
    simp only [id_tensorHom]
    rw [← MonoidalCategory.associator_monoidal_assoc]
    nth_rewrite 1 [← Category.id_comp (eComp V X.2 Y.2 Z.2)]
    rw [← tensorHom_comp_tensorHom_assoc]
    simp only [tensorHom_id]
    rw [MonoidalCategory.associator_naturality_assoc]

/-- The ordinary associator, with its stored genuine unit-graded
hom-object naturality. -/
@[no_expose] public def associatorGraded (d : EnrichedMonoidalCategoryData V I) :
    let leftProduct : EnrichedFunctor V ((I × I) × I) (I × I) :=
      { obj := fun X => (X.1.1 ⊗ X.1.2, X.2)
        map := fun X Y =>
          d.tensorMap X.1.1 Y.1.1 X.1.2 Y.1.2 ⊗ₘ
            𝟙 (X.2 ⟶[V] Y.2)
        map_id := by exact (prodEnrichedFunctor d.tensorEnrichedFunctor
          (EnrichedFunctor.id V I)).map_id
        map_comp := by exact (prodEnrichedFunctor d.tensorEnrichedFunctor
          (EnrichedFunctor.id V I)).map_comp }
    let left := leftProduct.comp V d.tensorEnrichedFunctor
    let right : EnrichedFunctor V ((I × I) × I) I :=
      { obj := fun X => X.1.1 ⊗ (X.1.2 ⊗ X.2)
        map := fun X Y =>
          (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2)
              (X.2 ⟶[V] Y.2)).hom ≫
            ((X.1.1 ⟶[V] Y.1.1) ◁
              d.tensorMap X.1.2 Y.1.2 X.2 Y.2) ≫
            d.tensorMap X.1.1 Y.1.1
              (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2)
        map_id := by exact d.associatorRightFunctor.map_id
        map_comp := by exact d.associatorRightFunctor.map_comp }
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) left right := by
  change GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    d.associatorLeftFunctor d.associatorRightFunctor
  exact
    { app := fun X => eHomEquiv V (α_ X.1.1 X.1.2 X.2).hom
      naturality := fun X Y => by
        dsimp only [Center.ofBraided, Center.ofBraidedObj,
          associatorLeftFunctor, associatorRightFunctor,
          prodEnrichedFunctor, tensorEnrichedFunctor,
          EnrichedFunctor.comp, EnrichedFunctor.id]
        rw [tensorHom_id]
        change (β_ (𝟙_ V)
              (((X.1.1 ⟶[V] Y.1.1) ⊗ (X.1.2 ⟶[V] Y.1.2)) ⊗
                (X.2 ⟶[V] Y.2))).hom ≫
              (((d.tensorMap X.1.1 Y.1.1 X.1.2 Y.1.2 ▷
                    (X.2 ⟶[V] Y.2)) ≫
                  d.tensorMap (X.1.1 ⊗ X.1.2) (Y.1.1 ⊗ Y.1.2)
                    X.2 Y.2) ⊗ₘ
                eHomEquiv V (α_ Y.1.1 Y.1.2 Y.2).hom) ≫
            eComp V ((X.1.1 ⊗ X.1.2) ⊗ X.2)
              ((Y.1.1 ⊗ Y.1.2) ⊗ Y.2)
              (Y.1.1 ⊗ (Y.1.2 ⊗ Y.2)) =
          (eHomEquiv V (α_ X.1.1 X.1.2 X.2).hom ⊗ₘ
              ((α_ (X.1.1 ⟶[V] Y.1.1)
                  (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom ≫
                ((X.1.1 ⟶[V] Y.1.1) ◁
                  d.tensorMap X.1.2 Y.1.2 X.2 Y.2) ≫
                d.tensorMap X.1.1 Y.1.1
                  (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2))) ≫
            eComp V ((X.1.1 ⊗ X.1.2) ⊗ X.2)
              (X.1.1 ⊗ (X.1.2 ⊗ X.2))
              (Y.1.1 ⊗ (Y.1.2 ⊗ Y.2))
        exact d.associatorNaturality
          X.1.1 Y.1.1 X.1.2 Y.1.2 X.2 Y.2 }

private theorem associatorGraded_app_private
    (d : EnrichedMonoidalCategoryData V I) (X : (I × I) × I) :
    d.associatorGraded.app X =
      eHomEquiv V (α_ X.1.1 X.1.2 X.2).hom :=
  rfl

/-- The component of the enriched associator is the selected ordinary
associator. -/
@[simp]
public theorem associatorGraded_app
    (d : EnrichedMonoidalCategoryData V I) (X : (I × I) × I) :
    d.associatorGraded.app X =
      eHomEquiv V (α_ X.1.1 X.1.2 X.2).hom :=
  associatorGraded_app_private d X

private def unitLeftProductFunctor :
    EnrichedFunctor V I (I × I) where
  obj i := (𝟙_ I, i)
  map i i' := (λ_ (i ⟶[V] i')).inv ≫
    (eId V (𝟙_ I) ⊗ₘ 𝟙 (i ⟶[V] i'))
  map_id i := by
    change eId V i ≫
        (λ_ (i ⟶[V] i)).inv ≫
          (eId V (𝟙_ I) ⊗ₘ 𝟙 (i ⟶[V] i)) =
      (λ_ (𝟙_ V)).inv ≫ (eId V (𝟙_ I) ⊗ₘ eId V i)
    rw [leftUnitor_inv_naturality_assoc]
    slice_lhs 2 3 =>
      rw [← id_tensorHom, tensorHom_comp_tensorHom]
      simp
  map_comp i j k := by
    change eComp V i j k ≫
        (λ_ (i ⟶[V] k)).inv ≫
          (eId V (𝟙_ I) ⊗ₘ 𝟙 (i ⟶[V] k)) =
      (((λ_ (i ⟶[V] j)).inv ≫
            (eId V (𝟙_ I) ⊗ₘ 𝟙 (i ⟶[V] j))) ⊗ₘ
          ((λ_ (j ⟶[V] k)).inv ≫
            (eId V (𝟙_ I) ⊗ₘ 𝟙 (j ⟶[V] k)))) ≫
        MonoidalCategory.tensorμ
          ((𝟙_ I) ⟶[V] (𝟙_ I)) (i ⟶[V] j)
          ((𝟙_ I) ⟶[V] (𝟙_ I)) (j ⟶[V] k) ≫
        (eComp V (𝟙_ I) (𝟙_ I) (𝟙_ I) ⊗ₘ eComp V i j k)
    rw [← cancel_epi (λ_ ((i ⟶[V] j) ⊗ (j ⟶[V] k))).hom]
    nth_rewrite 2 [MonoidalCategory.tensor_left_unitality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [MonoidalCategory.tensorμ_natural_assoc]
    rw [tensorHom_comp_tensorHom]
    simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rw [eId_tensor_eId_comp]
    nth_rewrite 2 [← Category.id_comp (eComp V i j k)]
    rw [← tensorHom_comp_tensorHom]
    simp only [tensorHom_id]
    rw [tensorHom_eq_leftUnitor_hom_comp]
    rw [← MonoidalCategory.leftUnitor_monoidal_assoc]
    rw [← MonoidalCategory.tensor_left_unitality_assoc]

private def unitRightProductFunctor :
    EnrichedFunctor V I (I × I) where
  obj i := (i, 𝟙_ I)
  map i i' := (ρ_ (i ⟶[V] i')).inv ≫
    (𝟙 (i ⟶[V] i') ⊗ₘ eId V (𝟙_ I))
  map_id i := by
    change eId V i ≫
        (ρ_ (i ⟶[V] i)).inv ≫
          (𝟙 (i ⟶[V] i) ⊗ₘ eId V (𝟙_ I)) =
      (λ_ (𝟙_ V)).inv ≫ (eId V i ⊗ₘ eId V (𝟙_ I))
    rw [rightUnitor_inv_naturality_assoc]
    rw [unitors_inv_equal]
    slice_lhs 2 3 =>
      rw [← tensorHom_id, tensorHom_comp_tensorHom]
      simp
  map_comp i j k := by
    change eComp V i j k ≫
        (ρ_ (i ⟶[V] k)).inv ≫
          (𝟙 (i ⟶[V] k) ⊗ₘ eId V (𝟙_ I)) =
      (((ρ_ (i ⟶[V] j)).inv ≫
            (𝟙 (i ⟶[V] j) ⊗ₘ eId V (𝟙_ I))) ⊗ₘ
          ((ρ_ (j ⟶[V] k)).inv ≫
            (𝟙 (j ⟶[V] k) ⊗ₘ eId V (𝟙_ I)))) ≫
        MonoidalCategory.tensorμ
          (i ⟶[V] j) ((𝟙_ I) ⟶[V] (𝟙_ I))
          (j ⟶[V] k) ((𝟙_ I) ⟶[V] (𝟙_ I)) ≫
        (eComp V i j k ⊗ₘ eComp V (𝟙_ I) (𝟙_ I) (𝟙_ I))
    rw [← cancel_epi (ρ_ ((i ⟶[V] j) ⊗ (j ⟶[V] k))).hom]
    nth_rewrite 2 [MonoidalCategory.tensor_right_unitality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [MonoidalCategory.tensorμ_natural_assoc]
    rw [tensorHom_comp_tensorHom]
    simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rw [eId_tensor_eId_comp]
    nth_rewrite 2 [← Category.id_comp (eComp V i j k)]
    rw [← tensorHom_comp_tensorHom]
    simp only [id_tensorHom]
    rw [tensorHom_eq_rightUnitor_hom_comp]
    rw [← MonoidalCategory.rightUnitor_monoidal_assoc]
    rw [← MonoidalCategory.tensor_right_unitality_assoc]

private def leftUnitorSourceFunctor
    (d : EnrichedMonoidalCategoryData V I) : EnrichedFunctor V I I :=
  unitLeftProductFunctor.comp V d.tensorEnrichedFunctor

private def rightUnitorSourceFunctor
    (d : EnrichedMonoidalCategoryData V I) : EnrichedFunctor V I I :=
  unitRightProductFunctor.comp V d.tensorEnrichedFunctor

/-- The ordinary left unitor with genuine unit-graded hom-object
naturality. -/
@[no_expose] public def leftUnitorGraded (d : EnrichedMonoidalCategoryData V I) :
    let sourceProduct : EnrichedFunctor V I (I × I) :=
      { obj := fun i => (𝟙_ I, i)
        map := fun i i' => (λ_ (i ⟶[V] i')).inv ≫
          (eId V (𝟙_ I) ⊗ₘ 𝟙 (i ⟶[V] i'))
        map_id := by exact unitLeftProductFunctor.map_id
        map_comp := by exact unitLeftProductFunctor.map_comp }
    let source := sourceProduct.comp V d.tensorEnrichedFunctor
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) source
      (EnrichedFunctor.id V I) := by
  change GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    d.leftUnitorSourceFunctor (EnrichedFunctor.id V I)
  exact
    { app := fun i => eHomEquiv V (λ_ i).hom
      naturality := fun i i' => by
        dsimp only [Center.ofBraided, Center.ofBraidedObj,
          leftUnitorSourceFunctor, unitLeftProductFunctor,
          tensorEnrichedFunctor, EnrichedFunctor.comp, EnrichedFunctor.id]
        simp only [Category.assoc]
        change (β_ (𝟙_ V) (i ⟶[V] i')).hom ≫
              (((λ_ (i ⟶[V] i')).inv ≫
                    (eId V (𝟙_ I) ⊗ₘ 𝟙 (i ⟶[V] i')) ≫
                  d.tensorMap (𝟙_ I) (𝟙_ I) i i') ⊗ₘ
                eHomEquiv V (λ_ i').hom) ≫
            eComp V (𝟙_ I ⊗ i) (𝟙_ I ⊗ i') i' =
          (eHomEquiv V (λ_ i).hom ⊗ₘ 𝟙 (i ⟶[V] i')) ≫
            eComp V (𝟙_ I ⊗ i) i i'
        exact d.leftUnitorNaturality i i' }

private theorem leftUnitorGraded_app_private
    (d : EnrichedMonoidalCategoryData V I) (i : I) :
    d.leftUnitorGraded.app i = eHomEquiv V (λ_ i).hom :=
  rfl

/-- The component of the enriched left unitor is the selected ordinary left
unitor. -/
@[simp]
public theorem leftUnitorGraded_app
    (d : EnrichedMonoidalCategoryData V I) (i : I) :
    d.leftUnitorGraded.app i = eHomEquiv V (λ_ i).hom :=
  leftUnitorGraded_app_private d i

/-- The ordinary right unitor with genuine unit-graded hom-object
naturality. -/
@[no_expose] public def rightUnitorGraded (d : EnrichedMonoidalCategoryData V I) :
    let sourceProduct : EnrichedFunctor V I (I × I) :=
      { obj := fun i => (i, 𝟙_ I)
        map := fun i i' => (ρ_ (i ⟶[V] i')).inv ≫
          (𝟙 (i ⟶[V] i') ⊗ₘ eId V (𝟙_ I))
        map_id := by exact unitRightProductFunctor.map_id
        map_comp := by exact unitRightProductFunctor.map_comp }
    let source := sourceProduct.comp V d.tensorEnrichedFunctor
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) source
      (EnrichedFunctor.id V I) := by
  change GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    d.rightUnitorSourceFunctor (EnrichedFunctor.id V I)
  exact
    { app := fun i => eHomEquiv V (ρ_ i).hom
      naturality := fun i i' => by
        dsimp only [Center.ofBraided, Center.ofBraidedObj,
          rightUnitorSourceFunctor, unitRightProductFunctor,
          tensorEnrichedFunctor, EnrichedFunctor.comp, EnrichedFunctor.id]
        simp only [Category.assoc]
        change (β_ (𝟙_ V) (i ⟶[V] i')).hom ≫
              (((ρ_ (i ⟶[V] i')).inv ≫
                    (𝟙 (i ⟶[V] i') ⊗ₘ eId V (𝟙_ I)) ≫
                  d.tensorMap i i' (𝟙_ I) (𝟙_ I)) ⊗ₘ
                eHomEquiv V (ρ_ i').hom) ≫
            eComp V (i ⊗ 𝟙_ I) (i' ⊗ 𝟙_ I) i' =
          (eHomEquiv V (ρ_ i).hom ⊗ₘ 𝟙 (i ⟶[V] i')) ≫
            eComp V (i ⊗ 𝟙_ I) i i'
        exact d.rightUnitorNaturality i i' }

private theorem rightUnitorGraded_app_private
    (d : EnrichedMonoidalCategoryData V I) (i : I) :
    d.rightUnitorGraded.app i = eHomEquiv V (ρ_ i).hom :=
  rfl

/-- The component of the enriched right unitor is the selected ordinary right
unitor. -/
@[simp]
public theorem rightUnitorGraded_app
    (d : EnrichedMonoidalCategoryData V I) (i : I) :
    d.rightUnitorGraded.app i = eHomEquiv V (ρ_ i).hom :=
  rightUnitorGraded_app_private d i

private def gradedToEnrichedNatTrans
    {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
    [BraidedCategory V]
    {C : Type uC} [EnrichedCategory V C]
    {D : Type uD} [Category.{vD} D] [EnrichedOrdinaryCategory V D]
    {F G : EnrichedFunctor V C D}
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) :
    EnrichedNatTrans F G := by
  let F' : EnrichedFunctor V (ForgetEnrichment V C) D := F
  let G' : EnrichedFunctor V (ForgetEnrichment V C) D := G
  let a' : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G' := a
  exact GradedNatTrans.toEnrichedNatTrans a'

private def enrichedNatTransIso
    {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
    {C : Type uC} [EnrichedCategory V C]
    {D : Type uD} [Category.{vD} D] [EnrichedOrdinaryCategory V D]
    {F G : EnrichedFunctor V C D} (a : EnrichedNatTrans F G)
    (e : ∀ X, F.forget.obj X ≅ G.forget.obj X)
    (h : ∀ X, a.out.app X = (e X).hom) : F ≅ G :=
  EnrichedFunctor.isoMk <| NatIso.ofComponents e fun f => by
    rw [← h, ← h]
    exact a.out.naturality f

/-- The enriched associator isomorphism. -/
@[no_expose] public def associatorIso (d : EnrichedMonoidalCategoryData V I) :
    let leftProduct : EnrichedFunctor V ((I × I) × I) (I × I) :=
      { obj := fun X => (X.1.1 ⊗ X.1.2, X.2)
        map := fun X Y =>
          d.tensorMap X.1.1 Y.1.1 X.1.2 Y.1.2 ⊗ₘ
            𝟙 (X.2 ⟶[V] Y.2)
        map_id := by exact (prodEnrichedFunctor d.tensorEnrichedFunctor
          (EnrichedFunctor.id V I)).map_id
        map_comp := by exact (prodEnrichedFunctor d.tensorEnrichedFunctor
          (EnrichedFunctor.id V I)).map_comp }
    let left := leftProduct.comp V d.tensorEnrichedFunctor
    let right : EnrichedFunctor V ((I × I) × I) I :=
      { obj := fun X => X.1.1 ⊗ (X.1.2 ⊗ X.2)
        map := fun X Y =>
          (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2)
              (X.2 ⟶[V] Y.2)).hom ≫
            ((X.1.1 ⟶[V] Y.1.1) ◁
              d.tensorMap X.1.2 Y.1.2 X.2 Y.2) ≫
            d.tensorMap X.1.1 Y.1.1
              (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2)
        map_id := by exact d.associatorRightFunctor.map_id
        map_comp := by exact d.associatorRightFunctor.map_comp }
    left ≅ right := by
  let a := gradedToEnrichedNatTrans (associatorGraded d)
  exact enrichedNatTransIso a
    (fun X => (ForgetEnrichment.equiv (D := I) V).inverse.mapIso
      (α_ (ForgetEnrichment.to V X).1.1
        (ForgetEnrichment.to V X).1.2 (ForgetEnrichment.to V X).2))
    (fun _ => rfl)

/-- The enriched left-unitor isomorphism. -/
@[no_expose] public def leftUnitorIso (d : EnrichedMonoidalCategoryData V I) :
    let sourceProduct : EnrichedFunctor V I (I × I) :=
      { obj := fun i => (𝟙_ I, i)
        map := fun i i' => (λ_ (i ⟶[V] i')).inv ≫
          (eId V (𝟙_ I) ⊗ₘ 𝟙 (i ⟶[V] i'))
        map_id := by exact unitLeftProductFunctor.map_id
        map_comp := by exact unitLeftProductFunctor.map_comp }
    let source := sourceProduct.comp V d.tensorEnrichedFunctor
    source ≅ EnrichedFunctor.id V I := by
  let a := gradedToEnrichedNatTrans (leftUnitorGraded d)
  exact enrichedNatTransIso a
    (fun X => (ForgetEnrichment.equiv (D := I) V).inverse.mapIso
      (λ_ (ForgetEnrichment.to V X)))
    (fun _ => rfl)

/-- The enriched right-unitor isomorphism. -/
@[no_expose] public def rightUnitorIso (d : EnrichedMonoidalCategoryData V I) :
    let sourceProduct : EnrichedFunctor V I (I × I) :=
      { obj := fun i => (i, 𝟙_ I)
        map := fun i i' => (ρ_ (i ⟶[V] i')).inv ≫
          (𝟙 (i ⟶[V] i') ⊗ₘ eId V (𝟙_ I))
        map_id := by exact unitRightProductFunctor.map_id
        map_comp := by exact unitRightProductFunctor.map_comp }
    let source := sourceProduct.comp V d.tensorEnrichedFunctor
    source ≅ EnrichedFunctor.id V I := by
  let a := gradedToEnrichedNatTrans (rightUnitorGraded d)
  exact enrichedNatTransIso a
    (fun X => (ForgetEnrichment.equiv (D := I) V).inverse.mapIso
      (ρ_ (ForgetEnrichment.to V X)))
    (fun _ => rfl)

/-- The enriched associator components satisfy the pentagon. -/
public theorem pentagon (_d : EnrichedMonoidalCategoryData V I)
    (W X Y Z : I) :
    eHomEquiv V (((α_ W X Y).hom ▷ Z) ≫
          (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom) =
      eHomEquiv V ((α_ (W ⊗ X) Y Z).hom ≫
        (α_ W X (Y ⊗ Z)).hom) := by
  rw [MonoidalCategory.pentagon]

/-- The enriched associator and unitor components satisfy the triangle. -/
public theorem triangle (_d : EnrichedMonoidalCategoryData V I) (X Y : I) :
    eHomEquiv V ((α_ X (𝟙_ I) Y).hom ≫ X ◁ (λ_ Y).hom) =
      eHomEquiv V ((ρ_ X).hom ▷ Y) := by
  rw [MonoidalCategory.triangle]

end EnrichedMonoidalCategoryData

variable [BraidedCategory I]

/-- Genuine enriched naturality data for the selected ordinary braiding. -/
public structure EnrichedBraidedMonoidalCategoryData
    (d : EnrichedMonoidalCategoryData V I) : Prop where
  /-- The braiding is natural on hom objects, not merely on ordinary arrows. -/
  braidingNaturality : ∀ i i' j j' : I,
    (β_ (𝟙_ V) ((i ⟶[V] i') ⊗ (j ⟶[V] j'))).hom ≫
          (d.tensorMap i i' j j' ⊗ₘ
            eHomEquiv V (β_ i' j').hom) ≫
        eComp V (i ⊗ j) (i' ⊗ j') (j' ⊗ i') =
      (eHomEquiv V (β_ i j).hom ⊗ₘ
          ((β_ (i ⟶[V] i') (j ⟶[V] j')).hom ≫
            d.tensorMap j j' i i')) ≫
        eComp V (i ⊗ j) (j ⊗ i) (j' ⊗ i')

namespace EnrichedBraidedMonoidalCategoryData

variable {V I} {d : EnrichedMonoidalCategoryData V I}

private def swappedTensorFunctor
    (b : EnrichedBraidedMonoidalCategoryData V I d) :
    EnrichedFunctor V (I × I) I :=
  EnrichedFunctor.ofRawIsoComponents d.tensorEnrichedFunctor
    (fun X => X.2 ⊗ X.1)
    (fun X Y => (β_ (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)).hom ≫
      d.tensorMap X.2 Y.2 X.1 Y.1)
    (fun X => β_ X.1 X.2)
    (fun X Y => by
      change (β_ (𝟙_ V)
            ((X.1 ⟶[V] Y.1) ⊗ (X.2 ⟶[V] Y.2))).hom ≫
            (d.tensorMap X.1 Y.1 X.2 Y.2 ⊗ₘ
              eHomEquiv V (β_ Y.1 Y.2).hom) ≫
          eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) (Y.2 ⊗ Y.1) =
        (eHomEquiv V (β_ X.1 X.2).hom ⊗ₘ
            ((β_ (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)).hom ≫
              d.tensorMap X.2 Y.2 X.1 Y.1)) ≫
          eComp V (X.1 ⊗ X.2) (X.2 ⊗ X.1) (Y.2 ⊗ Y.1)
      exact b.braidingNaturality X.1 Y.1 X.2 Y.2)

/-- The ordinary braiding with its stored genuine unit-graded hom-object
naturality. -/
@[no_expose] public def braidingGraded (b : EnrichedBraidedMonoidalCategoryData V I d) :
    let swapped : EnrichedFunctor V (I × I) I :=
      { obj := fun X => X.2 ⊗ X.1
        map := fun X Y =>
          (β_ (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)).hom ≫
            d.tensorMap X.2 Y.2 X.1 Y.1
        map_id := by exact (swappedTensorFunctor b).map_id
        map_comp := by exact (swappedTensorFunctor b).map_comp }
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      d.tensorEnrichedFunctor swapped := by
  change GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    d.tensorEnrichedFunctor (swappedTensorFunctor b)
  exact
    { app := fun X => eHomEquiv V (β_ X.1 X.2).hom
      naturality := fun X Y => by
        dsimp only [Center.ofBraided, Center.ofBraidedObj,
          EnrichedMonoidalCategoryData.tensorEnrichedFunctor,
          swappedTensorFunctor, EnrichedFunctor.ofRawIsoComponents]
        change (β_ (𝟙_ V)
              ((X.1 ⟶[V] Y.1) ⊗ (X.2 ⟶[V] Y.2))).hom ≫
              (d.tensorMap X.1 Y.1 X.2 Y.2 ⊗ₘ
                eHomEquiv V (β_ Y.1 Y.2).hom) ≫
            eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) (Y.2 ⊗ Y.1) =
          (eHomEquiv V (β_ X.1 X.2).hom ⊗ₘ
              ((β_ (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)).hom ≫
                d.tensorMap X.2 Y.2 X.1 Y.1)) ≫
            eComp V (X.1 ⊗ X.2) (X.2 ⊗ X.1) (Y.2 ⊗ Y.1)
        exact b.braidingNaturality X.1 Y.1 X.2 Y.2 }

private theorem braidingGraded_app_private
    (b : EnrichedBraidedMonoidalCategoryData V I d) (X : I × I) :
    b.braidingGraded.app X = eHomEquiv V (β_ X.1 X.2).hom :=
  rfl

/-- The component of the enriched braiding is the selected ordinary
braiding. -/
@[simp]
public theorem braidingGraded_app
    (b : EnrichedBraidedMonoidalCategoryData V I d) (X : I × I) :
    b.braidingGraded.app X = eHomEquiv V (β_ X.1 X.2).hom :=
  braidingGraded_app_private b X

/-- The enriched braiding isomorphism. -/
@[no_expose] public def braidingIso (b : EnrichedBraidedMonoidalCategoryData V I d) :
    let swapped : EnrichedFunctor V (I × I) I :=
      { obj := fun X => X.2 ⊗ X.1
        map := fun X Y =>
          (β_ (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)).hom ≫
            d.tensorMap X.2 Y.2 X.1 Y.1
        map_id := by exact (swappedTensorFunctor b).map_id
        map_comp := by exact (swappedTensorFunctor b).map_comp }
    d.tensorEnrichedFunctor ≅ swapped := by
  let a := EnrichedMonoidalCategoryData.gradedToEnrichedNatTrans
    (braidingGraded b)
  exact EnrichedMonoidalCategoryData.enrichedNatTransIso a
    (fun X => (ForgetEnrichment.equiv (D := I) V).inverse.mapIso
      (β_ (ForgetEnrichment.to V X).1 (ForgetEnrichment.to V X).2))
    (fun _ => rfl)

/-- The enriched braiding components satisfy the forward hexagon. -/
public theorem hexagonForward
    (_b : EnrichedBraidedMonoidalCategoryData V I d) (X Y Z : I) :
    eHomEquiv V ((α_ X Y Z).hom ≫
          (β_ X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom) =
      eHomEquiv V (((β_ X Y).hom ▷ Z) ≫
        (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom) := by
  rw [BraidedCategory.hexagon_forward]

/-- The enriched braiding components satisfy the reverse hexagon. -/
public theorem hexagonReverse
    (_b : EnrichedBraidedMonoidalCategoryData V I d) (X Y Z : I) :
    eHomEquiv V ((α_ X Y Z).inv ≫
          (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv) =
      eHomEquiv V ((X ◁ (β_ Y Z).hom) ≫
        (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y) := by
  rw [BraidedCategory.hexagon_reverse]

end EnrichedBraidedMonoidalCategoryData

end CategoryTheory

namespace CategoryTheory

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable (I : Type uI) [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [SymmetricCategory I]

/-- Enriched symmetric monoidal data has no field beyond the enriched
braiding datum; symmetry is a theorem. -/
public abbrev EnrichedSymmetricMonoidalCategoryData
    (d : EnrichedMonoidalCategoryData V I) :=
  EnrichedBraidedMonoidalCategoryData V I d

namespace EnrichedSymmetricMonoidalCategoryData

variable {V I} {d : EnrichedMonoidalCategoryData V I}

/-- Double enriched braiding is the identity. -/
public theorem symmetry
    (_b : EnrichedSymmetricMonoidalCategoryData V I d) (X Y : I) :
    eHomEquiv V ((β_ X Y).hom ≫ (β_ Y X).hom) =
      eId V (X ⊗ Y) := by
  calc
    _ = eHomEquiv V (𝟙 (X ⊗ Y)) :=
      congrArg (eHomEquiv V) (SymmetricCategory.symmetry X Y)
    _ = _ := eHomEquiv_id V (X ⊗ Y)

end EnrichedSymmetricMonoidalCategoryData

namespace MonoidalClosed

open scoped MonoidalClosed

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]

private def selfTensorMap (X X' Y Y' : V) :
    ((ihom X).obj X' ⊗ (ihom Y).obj Y') ⟶
      (ihom (X ⊗ Y)).obj (X' ⊗ Y') :=
  MonoidalClosed.curry <|
    (MonoidalCategory.tensorμ X Y
        ((ihom X).obj X') ((ihom Y).obj Y') ≫
      ((ihom.ev X).app X' ⊗ₘ (ihom.ev Y).app Y'))

private theorem selfTensorMap_eHomEquiv
    {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y') :
    (λ_ (𝟙_ V)).inv ≫
          (eHomEquiv V f ⊗ₘ eHomEquiv V g) ≫
        selfTensorMap V X X' Y Y' =
      eHomEquiv V (f ⊗ₘ g) := by
  apply MonoidalClosed.uncurry'_injective
  simp only [selfTensorMap,
    MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv,
    MonoidalClosed.uncurry', MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  slice_lhs 3 5 =>
    rw [MonoidalCategory.tensorμ_natural_right_assoc X Y
      (MonoidalClosed.curry' f) (MonoidalClosed.curry' g)]
  rw [tensorHom_comp_tensorHom]
  rw [MonoidalClosed.whiskerLeft_curry'_ihom_ev_app,
    MonoidalClosed.whiskerLeft_curry'_ihom_ev_app]
  rw [← tensorHom_comp_tensorHom]
  rw [← MonoidalCategory.tensor_right_unitality_assoc]
  simp
  simpa only [MonoidalClosed.uncurry'] using
    (MonoidalClosed.uncurry'_curry' (f ⊗ₘ g)).symm

private theorem unitGradedNaturality_of_whisker
    {P Q R S H : V}
    (f : H ⟶ @EnrichedCategory.Hom V _ _ V
      (MonoidalClosed.enrichedCategorySelf V) P Q)
    (g : H ⟶ @EnrichedCategory.Hom V _ _ V
      (MonoidalClosed.enrichedCategorySelf V) R S)
    (a : P ⟶ R) (b : Q ⟶ S)
    (h : f ≫ eHomWhiskerLeft V P b =
      g ≫ eHomWhiskerRight V a S) :
    (β_ (𝟙_ V) H).hom ≫
          (f ⊗ₘ eHomEquiv V b) ≫ eComp V P Q S =
      (eHomEquiv V a ⊗ₘ g) ≫ eComp V P R S := by
  apply (cancel_epi (λ_ H).inv).1
  rw [leftUnitor_inv_braiding_assoc]
  rw [tensorHom_def_assoc]
  rw [← rightUnitor_inv_naturality_assoc]
  rw [tensorHom_def_assoc]
  rw [← whisker_exchange_assoc]
  rw [← leftUnitor_inv_naturality_assoc]
  simpa only [eHomWhiskerLeft, eHomWhiskerRight, Category.assoc] using h


/-- The canonical enriched monoidal datum on a braided closed category's
self-enrichment. -/
@[no_expose] public def enrichedMonoidalCategoryDataSelf :
    EnrichedMonoidalCategoryData V V where
  tensorMap := selfTensorMap V
  tensorMap_comp := by
    intro X X' X'' Y Y' Y''
    change
      (MonoidalCategory.tensorμ
            ((ihom X).obj X') ((ihom Y).obj Y')
            ((ihom X').obj X'') ((ihom Y').obj Y'') ≫
          (MonoidalClosed.comp X X' X'' ⊗ₘ
            MonoidalClosed.comp Y Y' Y'')) ≫
        selfTensorMap V X X'' Y Y'' =
      (selfTensorMap V X X' Y Y' ⊗ₘ
          selfTensorMap V X' X'' Y' Y'') ≫
        MonoidalClosed.comp (X ⊗ Y) (X' ⊗ Y') (X'' ⊗ Y'')
    apply MonoidalClosed.uncurry_injective
    simp only [selfTensorMap, MonoidalClosed.comp_eq,
      MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_curry]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [MonoidalCategory.tensorμ_natural_right_assoc X Y
      (MonoidalClosed.curry (MonoidalClosed.compTranspose X X' X''))
      (MonoidalClosed.curry (MonoidalClosed.compTranspose Y Y' Y''))]
    rw [tensorHom_comp_tensorHom]
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app,
      MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    simp only [MonoidalClosed.compTranspose_eq]
    conv_rhs =>
      simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp,
        Category.assoc]
    rw [associator_inv_naturality_right_assoc]
    rw [associator_inv_naturality_middle_assoc]
    rw [whisker_exchange_assoc]
    rw [← comp_whiskerRight_assoc]
    rw [← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry]
    dsimp
    rw [← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry]
    conv_rhs =>
      rw [← tensorHom_def, ← tensorHom_def]
    rw [← cancel_epi
      (α_ (X ⊗ Y)
        ((ihom X).obj X' ⊗ (ihom Y).obj Y')
        ((ihom X').obj X'' ⊗ (ihom Y').obj Y'')).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.tensor_associativity_assoc]
    rw [tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id_assoc]
    rw [comp_whiskerRight_assoc]
    rw [MonoidalCategory.tensorμ_natural_left_assoc]
    rw [tensorHom_comp_tensorHom]
  tensorMap_eHomEquiv := selfTensorMap_eHomEquiv V
  associatorNaturality := by
    intro X X' Y Y' Z Z'
    change
      (β_ (𝟙_ V)
                (((ihom X).obj X' ⊗ (ihom Y).obj Y') ⊗
                  (ihom Z).obj Z')).hom ≫
                (((selfTensorMap V X X' Y Y' ▷ (ihom Z).obj Z') ≫
                    selfTensorMap V (X ⊗ Y) (X' ⊗ Y') Z Z') ⊗ₘ
                  eHomEquiv V (α_ X' Y' Z').hom) ≫
              eComp V ((X ⊗ Y) ⊗ Z) ((X' ⊗ Y') ⊗ Z')
                (X' ⊗ (Y' ⊗ Z')) =
            (eHomEquiv V (α_ X Y Z).hom ⊗ₘ
                ((α_ ((ihom X).obj X') ((ihom Y).obj Y')
                    ((ihom Z).obj Z')).hom ≫
                  ((ihom X).obj X' ◁ selfTensorMap V Y Y' Z Z') ≫
                  selfTensorMap V X X' (Y ⊗ Z) (Y' ⊗ Z'))) ≫
              eComp V ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
                (X' ⊗ (Y' ⊗ Z'))
    apply unitGradedNaturality_of_whisker V
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
    apply MonoidalClosed.uncurry_injective
    simp only [selfTensorMap, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_ihom_map,
      MonoidalClosed.uncurry_pre]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app_assoc]
    rw [← tensorHom_id]
    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [MonoidalCategory.tensorμ_natural_right]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    have hExchange :
        ((X ⊗ Y) ⊗ Z) ◁
              MonoidalClosed.curry
                (MonoidalCategory.tensorμ X (Y ⊗ Z)
                    ((ihom X).obj X')
                    ((ihom (Y ⊗ Z)).obj (Y' ⊗ Z')) ≫
                  ((ihom.ev X).app X' ⊗ₘ
                    (ihom.ev (Y ⊗ Z)).app (Y' ⊗ Z'))) ≫
            (α_ X Y Z).hom ▷
                (ihom (X ⊗ (Y ⊗ Z))).obj (X' ⊗ (Y' ⊗ Z')) ≫
              (ihom.ev (X ⊗ (Y ⊗ Z))).app (X' ⊗ (Y' ⊗ Z')) =
          (α_ X Y Z).hom ▷
                (((ihom X).obj X') ⊗
                  ((ihom (Y ⊗ Z)).obj (Y' ⊗ Z'))) ≫
            (X ⊗ (Y ⊗ Z)) ◁
                MonoidalClosed.curry
                  (MonoidalCategory.tensorμ X (Y ⊗ Z)
                      ((ihom X).obj X')
                      ((ihom (Y ⊗ Z)).obj (Y' ⊗ Z')) ≫
                    ((ihom.ev X).app X' ⊗ₘ
                      (ihom.ev (Y ⊗ Z)).app (Y' ⊗ Z'))) ≫
              (ihom.ev (X ⊗ (Y ⊗ Z))).app (X' ⊗ (Y' ⊗ Z')) := by
      simpa only [Functor.id_obj] using
        (whisker_exchange_assoc
          (f := (α_ X Y Z).hom)
          (g := MonoidalClosed.curry
            (MonoidalCategory.tensorμ X (Y ⊗ Z)
                ((ihom X).obj X')
                ((ihom (Y ⊗ Z)).obj (Y' ⊗ Z')) ≫
              ((ihom.ev X).app X' ⊗ₘ
                (ihom.ev (Y ⊗ Z)).app (Y' ⊗ Z'))))
          (h := (ihom.ev (X ⊗ (Y ⊗ Z))).app
            (X' ⊗ (Y' ⊗ Z'))))
    rw [hExchange]
    have hEval :
        (X ⊗ (Y ⊗ Z)) ◁
              MonoidalClosed.curry
                (MonoidalCategory.tensorμ X (Y ⊗ Z)
                    ((ihom X).obj X')
                    ((ihom (Y ⊗ Z)).obj (Y' ⊗ Z')) ≫
                  ((ihom.ev X).app X' ⊗ₘ
                    (ihom.ev (Y ⊗ Z)).app (Y' ⊗ Z'))) ≫
            (ihom.ev (X ⊗ (Y ⊗ Z))).app (X' ⊗ (Y' ⊗ Z')) =
          MonoidalCategory.tensorμ X (Y ⊗ Z)
              ((ihom X).obj X')
              ((ihom (Y ⊗ Z)).obj (Y' ⊗ Z')) ≫
            ((ihom.ev X).app X' ⊗ₘ
              (ihom.ev (Y ⊗ Z)).app (Y' ⊗ Z')) := by
      simpa only [Functor.id_obj] using
        (MonoidalClosed.whiskerLeft_curry_ihom_ev_app
          (g := MonoidalCategory.tensorμ X (Y ⊗ Z)
              ((ihom X).obj X')
              ((ihom (Y ⊗ Z)).obj (Y' ⊗ Z')) ≫
            ((ihom.ev X).app X' ⊗ₘ
              (ihom.ev (Y ⊗ Z)).app (Y' ⊗ Z'))))
    rw [hEval]
    have hFactorL :
        (MonoidalCategory.tensorμ X Y
              ((ihom X).obj X') ((ihom Y).obj Y') ≫
            ((ihom.ev X).app X' ⊗ₘ (ihom.ev Y).app Y')) ⊗ₘ
            (ihom.ev Z).app Z' =
          (MonoidalCategory.tensorμ X Y
              ((ihom X).obj X') ((ihom Y).obj Y') ▷
                (Z ⊗ (ihom Z).obj Z')) ≫
            (((ihom.ev X).app X' ⊗ₘ (ihom.ev Y).app Y') ⊗ₘ
              (ihom.ev Z).app Z') := by
      rw [← tensorHom_id]
      rw [tensorHom_comp_tensorHom]
      simp
    rw [hFactorL]
    have hAssocEval :
        (((ihom.ev X).app X' ⊗ₘ (ihom.ev Y).app Y') ⊗ₘ
              (ihom.ev Z).app Z') ≫
            (α_ X' Y' Z').hom =
          (α_ ((ihom X ⋙ tensorLeft X).obj X')
            ((ihom Y ⋙ tensorLeft Y).obj Y')
            ((ihom Z ⋙ tensorLeft Z).obj Z')).hom ≫
            ((ihom.ev X).app X' ⊗ₘ
              ((ihom.ev Y).app Y' ⊗ₘ (ihom.ev Z).app Z')) := by
      exact
        (MonoidalCategory.associator_naturality
          ((ihom.ev X).app X') ((ihom.ev Y).app Y')
          ((ihom.ev Z).app Z'))
    simp only [Category.assoc]
    rw [hAssocEval]
    rw [whisker_exchange_assoc]
    rw [whisker_exchange_assoc]
    rw [← tensorHom_def_assoc]
    nth_rewrite 2 [← id_tensorHom]
    rw [MonoidalCategory.tensorμ_natural_right_assoc]
    rw [tensorHom_comp_tensorHom]
    simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    have hFactorR :
        (ihom.ev X).app X' ⊗ₘ
            (MonoidalCategory.tensorμ Y Z
                ((ihom Y).obj Y') ((ihom Z).obj Z') ≫
              ((ihom.ev Y).app Y' ⊗ₘ (ihom.ev Z).app Z')) =
          (X ⊗ (ihom X).obj X') ◁
              MonoidalCategory.tensorμ Y Z
                ((ihom Y).obj Y') ((ihom Z).obj Z') ≫
            ((ihom.ev X).app X' ⊗ₘ
              ((ihom.ev Y).app Y' ⊗ₘ (ihom.ev Z).app Z')) := by
      rw [← id_tensorHom]
      rw [tensorHom_comp_tensorHom]
      simp
    rw [hFactorR]
    have hAssocSource :
        (α_ ((ihom X ⋙ tensorLeft X).obj X')
            ((ihom Y ⋙ tensorLeft Y).obj Y')
            ((ihom Z ⋙ tensorLeft Z).obj Z')).hom =
          (α_ (X ⊗ (ihom X).obj X')
            (Y ⊗ (ihom Y).obj Y')
            (Z ⊗ (ihom Z).obj Z')).hom := rfl
    rw [hAssocSource]
    rw [MonoidalCategory.associator_monoidal_assoc]
  leftUnitorNaturality := by
    intro X X'
    change
      (β_ (𝟙_ V) ((ihom X).obj X')).hom ≫
                (((λ_ ((ihom X).obj X')).inv ≫
                      (eId V (𝟙_ V) ⊗ₘ 𝟙 ((ihom X).obj X')) ≫
                    selfTensorMap V (𝟙_ V) (𝟙_ V) X X') ⊗ₘ
                  eHomEquiv V (λ_ X').hom) ≫
              eComp V ((𝟙_ V) ⊗ X) ((𝟙_ V) ⊗ X') X' =
            (eHomEquiv V (λ_ X).hom ⊗ₘ 𝟙 ((ihom X).obj X')) ≫
              eComp V ((𝟙_ V) ⊗ X) X X'
    apply unitGradedNaturality_of_whisker V
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
    apply MonoidalClosed.uncurry_injective
    simp only [selfTensorMap, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_ihom_map, MonoidalClosed.uncurry_pre]
    simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app_assoc]
    rw [MonoidalClosed.enrichedCategorySelf_id]
    rw [MonoidalClosed.id_eq]
    slice_lhs 2 4 =>
      rw [MonoidalCategory.tensorμ_natural_right_assoc (𝟙_ V) X
        (MonoidalClosed.curry (ρ_ (𝟙_ V)).hom)
        (𝟙 ((ihom X).obj X'))]
    slice_lhs 3 4 =>
      rw [tensorHom_comp_tensorHom]
    simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    rw [tensorHom_def_assoc]
    slice_lhs 4 5 =>
      rw [leftUnitor_naturality]
    rw [← unitors_equal]
    rw [← MonoidalCategory.leftUnitor_monoidal_assoc]
    rw [← id_tensorHom]
    rw [tensorHom_comp_tensorHom_assoc]
    simp
  rightUnitorNaturality := by
    intro X X'
    change
      (β_ (𝟙_ V) ((ihom X).obj X')).hom ≫
                (((ρ_ ((ihom X).obj X')).inv ≫
                      (𝟙 ((ihom X).obj X') ⊗ₘ eId V (𝟙_ V)) ≫
                    selfTensorMap V X X' (𝟙_ V) (𝟙_ V)) ⊗ₘ
                  eHomEquiv V (ρ_ X').hom) ≫
              eComp V (X ⊗ (𝟙_ V)) (X' ⊗ (𝟙_ V)) X' =
            (eHomEquiv V (ρ_ X).hom ⊗ₘ 𝟙 ((ihom X).obj X')) ≫
              eComp V (X ⊗ (𝟙_ V)) X X'
    apply unitGradedNaturality_of_whisker V
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
    apply MonoidalClosed.uncurry_injective
    simp only [selfTensorMap, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_ihom_map, MonoidalClosed.uncurry_pre]
    simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app_assoc]
    rw [MonoidalClosed.enrichedCategorySelf_id]
    rw [MonoidalClosed.id_eq]
    slice_lhs 2 4 =>
      rw [MonoidalCategory.tensorμ_natural_right_assoc X (𝟙_ V)
        (𝟙 ((ihom X).obj X'))
        (MonoidalClosed.curry (ρ_ (𝟙_ V)).hom)]
    slice_lhs 3 4 =>
      rw [tensorHom_comp_tensorHom]
    simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    rw [tensorHom_def'_assoc]
    slice_lhs 4 5 =>
      rw [rightUnitor_naturality]
    rw [← unitors_equal]
    rw [← MonoidalCategory.rightUnitor_monoidal_assoc]
    rw [← id_tensorHom]
    rw [tensorHom_comp_tensorHom_assoc]
    simp

private theorem enrichedMonoidalCategoryDataSelf_tensorMap_private
    (X X' Y Y' : V) :
    (enrichedMonoidalCategoryDataSelf V).tensorMap X X' Y Y' =
      MonoidalClosed.curry
        (MonoidalCategory.tensorμ X Y
            ((ihom X).obj X') ((ihom Y).obj Y') ≫
          ((ihom.ev X).app X' ⊗ₘ (ihom.ev Y).app Y')) :=
  rfl

/-- The tensor map of the canonical closed self-enrichment is the transpose
of the two evaluation maps after monoidal interchange. -/
public theorem enrichedMonoidalCategoryDataSelf_tensorMap
    (X X' Y Y' : V) :
    (enrichedMonoidalCategoryDataSelf V).tensorMap X X' Y Y' =
      MonoidalClosed.curry
        (MonoidalCategory.tensorμ X Y
            ((ihom X).obj X') ((ihom Y).obj Y') ≫
          ((ihom.ev X).app X' ⊗ₘ (ihom.ev Y).app Y')) :=
  enrichedMonoidalCategoryDataSelf_tensorMap_private V X X' Y Y'

end MonoidalClosed

namespace EnrichedFunctor

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {C : Type uC} [EnrichedCategory V C]
variable {D : Type uD} [EnrichedCategory V D]

/-- The external tensor of two enriched functors with values in a braided
closed category. -/
public def externalTensor (F : EnrichedFunctor V C V)
    (G : EnrichedFunctor V D V) : EnrichedFunctor V (C × D) V where
  obj X := F.obj X.1 ⊗ G.obj X.2
  map X Y := (F.map X.1 Y.1 ⊗ₘ G.map X.2 Y.2) ≫
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
      (F.obj X.1) (F.obj Y.1) (G.obj X.2) (G.obj Y.2)
  map_id X := by
    exact ((prodEnrichedFunctor F G).comp V
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorEnrichedFunctor).map_id X
  map_comp X Y Z := by
    exact ((prodEnrichedFunctor F G).comp V
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorEnrichedFunctor).map_comp X Y Z

/-- The external tensor is objectwise the selected tensor. -/
@[simp]
public theorem externalTensor_obj (F : EnrichedFunctor V C V)
    (G : EnrichedFunctor V D V) (X : C × D) :
    (externalTensor F G).obj X = F.obj X.1 ⊗ G.obj X.2 :=
  rfl

/-- The external tensor map tensors the two enriched maps and then applies
the canonical self-enriched tensor map. -/
public theorem externalTensor_map (F : EnrichedFunctor V C V)
    (G : EnrichedFunctor V D V) (X Y : C × D) :
    (externalTensor F G).map X Y =
      (F.map X.1 Y.1 ⊗ₘ G.map X.2 Y.2) ≫
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
          (F.obj X.1) (F.obj Y.1) (G.obj X.2) (G.obj Y.2) :=
  rfl

end EnrichedFunctor

end CategoryTheory
