/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic

/-!
# Tests for enriched monoidal category data

These tests pin the product-enrichment orientation, the genuine graded
constraint data, the named braided and symmetric extensions, and the closed
self-enrichment used by external tensor products.

## Public endpoint and export tests

This owner intentionally imports only `Monoidal.Basic`.  The clients below
reconstruct every constraint endpoint from exported declarations and check
the four public isomorphisms against those independently spelled endpoints.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory.MonoidalCategory

universe uV vV uC vC uD vD uI vI

namespace CategoryTheory

namespace PublicEndpointClients

attribute [local instance] Enriched.prodCategory

private def clientProductFunctor
    {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
    [BraidedCategory V]
    {A : Type uC} [EnrichedCategory V A]
    {B : Type uD} [EnrichedCategory V B]
    {C : Type uI} [EnrichedCategory V C]
    {D : Type vI} [EnrichedCategory V D]
    (L : EnrichedFunctor V A B) (R : EnrichedFunctor V C D) :
    EnrichedFunctor V (A × C) (B × D) where
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

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

private def clientAssociatorLeft
    (d : EnrichedMonoidalCategoryData V I) :
    EnrichedFunctor V ((I × I) × I) I :=
  (clientProductFunctor d.tensorEnrichedFunctor
      (EnrichedFunctor.id V I)).comp V d.tensorEnrichedFunctor

private def clientAssociatorRight
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

omit [BraidedCategory V] [MonoidalCategory I] in
private theorem clientEIdTensorEIdComp (i : I) :
    (eId V i ⊗ₘ eId V i) ≫ eComp V i i i =
      (λ_ (𝟙_ V)).hom ≫ eId V i := by
  rw [← cancel_epi (λ_ (𝟙_ V)).inv]
  simp only [Iso.inv_hom_id_assoc]
  rw [leftUnitor_inv_comp_tensorHom_assoc]
  rw [e_id_comp, Category.comp_id]

omit [BraidedCategory V] in
private theorem clientTensorHomEqLeftUnitor
    {X Y Z : V} (f : 𝟙_ V ⟶ Y) (g : X ⟶ Z) :
    f ⊗ₘ g =
      (λ_ X).hom ≫ g ≫ (λ_ Z).inv ≫ f ▷ Z := by
  rw [← cancel_epi (λ_ X).inv]
  simp only [Iso.inv_hom_id_assoc]
  exact leftUnitor_inv_comp_tensorHom f g

omit [BraidedCategory V] in
private theorem clientTensorHomEqRightUnitor
    {X Y Z : V} (f : X ⟶ Y) (g : 𝟙_ V ⟶ Z) :
    f ⊗ₘ g =
      (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv ≫ Y ◁ g := by
  rw [← cancel_epi (ρ_ X).inv]
  simp only [Iso.inv_hom_id_assoc]
  exact rightUnitor_inv_comp_tensorHom f g

private def clientUnitLeftProduct : EnrichedFunctor V I (I × I) where
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
    rw [clientEIdTensorEIdComp]
    nth_rewrite 2 [← Category.id_comp (eComp V i j k)]
    rw [← tensorHom_comp_tensorHom]
    simp only [tensorHom_id]
    rw [clientTensorHomEqLeftUnitor]
    rw [← MonoidalCategory.leftUnitor_monoidal_assoc]
    rw [← MonoidalCategory.tensor_left_unitality_assoc]

private def clientUnitRightProduct : EnrichedFunctor V I (I × I) where
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
    rw [clientEIdTensorEIdComp]
    nth_rewrite 2 [← Category.id_comp (eComp V i j k)]
    rw [← tensorHom_comp_tensorHom]
    simp only [id_tensorHom]
    rw [clientTensorHomEqRightUnitor]
    rw [← MonoidalCategory.rightUnitor_monoidal_assoc]
    rw [← MonoidalCategory.tensor_right_unitality_assoc]

private def clientLeftUnitorSource
    (d : EnrichedMonoidalCategoryData V I) : EnrichedFunctor V I I :=
  clientUnitLeftProduct.comp V d.tensorEnrichedFunctor

private def clientRightUnitorSource
    (d : EnrichedMonoidalCategoryData V I) : EnrichedFunctor V I I :=
  clientUnitRightProduct.comp V d.tensorEnrichedFunctor

section MonoidalClients

variable (d : EnrichedMonoidalCategoryData V I)

example : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (clientAssociatorLeft d) (clientAssociatorRight d) :=
  d.associatorGraded

example : clientAssociatorLeft d ≅ clientAssociatorRight d :=
  d.associatorIso

example : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (clientLeftUnitorSource d) (EnrichedFunctor.id V I) :=
  d.leftUnitorGraded

example : clientLeftUnitorSource d ≅ EnrichedFunctor.id V I :=
  d.leftUnitorIso

example : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (clientRightUnitorSource d) (EnrichedFunctor.id V I) :=
  d.rightUnitorGraded

example : clientRightUnitorSource d ≅ EnrichedFunctor.id V I :=
  d.rightUnitorIso

example (X : (I × I) × I) :
    eId V X ≫ (clientAssociatorLeft d).map X X =
      eId V ((clientAssociatorLeft d).obj X) :=
  (clientAssociatorLeft d).map_id X

example (X Y Z : (I × I) × I) :
    eComp V X Y Z ≫ (clientAssociatorLeft d).map X Z =
      ((clientAssociatorLeft d).map X Y ⊗ₘ
        (clientAssociatorLeft d).map Y Z) ≫
      eComp V ((clientAssociatorLeft d).obj X)
        ((clientAssociatorLeft d).obj Y)
        ((clientAssociatorLeft d).obj Z) :=
  (clientAssociatorLeft d).map_comp X Y Z

example (X : (I × I) × I) :
    eId V X ≫ (clientAssociatorRight d).map X X =
      eId V ((clientAssociatorRight d).obj X) :=
  (clientAssociatorRight d).map_id X

example (X Y Z : (I × I) × I) :
    eComp V X Y Z ≫ (clientAssociatorRight d).map X Z =
      ((clientAssociatorRight d).map X Y ⊗ₘ
        (clientAssociatorRight d).map Y Z) ≫
      eComp V ((clientAssociatorRight d).obj X)
        ((clientAssociatorRight d).obj Y)
        ((clientAssociatorRight d).obj Z) :=
  (clientAssociatorRight d).map_comp X Y Z

example (X : I) :
    eId V X ≫ (clientLeftUnitorSource d).map X X =
      eId V ((clientLeftUnitorSource d).obj X) :=
  (clientLeftUnitorSource d).map_id X

example (X Y Z : I) :
    eComp V X Y Z ≫ (clientLeftUnitorSource d).map X Z =
      ((clientLeftUnitorSource d).map X Y ⊗ₘ
        (clientLeftUnitorSource d).map Y Z) ≫
      eComp V ((clientLeftUnitorSource d).obj X)
        ((clientLeftUnitorSource d).obj Y)
        ((clientLeftUnitorSource d).obj Z) :=
  (clientLeftUnitorSource d).map_comp X Y Z

example (X : I) :
    eId V X ≫ (clientRightUnitorSource d).map X X =
      eId V ((clientRightUnitorSource d).obj X) :=
  (clientRightUnitorSource d).map_id X

example (X Y Z : I) :
    eComp V X Y Z ≫ (clientRightUnitorSource d).map X Z =
      ((clientRightUnitorSource d).map X Y ⊗ₘ
        (clientRightUnitorSource d).map Y Z) ≫
      eComp V ((clientRightUnitorSource d).obj X)
        ((clientRightUnitorSource d).obj Y)
        ((clientRightUnitorSource d).obj Z) :=
  (clientRightUnitorSource d).map_comp X Y Z

end MonoidalClients

omit [BraidedCategory V] [MonoidalCategory I] in
private theorem clientMapEqCompEHomCongr
    {P Q R S : I} {H : V}
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

omit [BraidedCategory V] [MonoidalCategory I] in
@[reassoc]
private theorem clientECompCompEHomCongr
    {X Y Z X' Y' Z' : I}
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

omit [BraidedCategory V] [MonoidalCategory I] in
private def clientConjugateEnrichedFunctor
    {C : Type uC} [EnrichedCategory V C]
    (F : EnrichedFunctor V C I) (Gobj : C → I)
    (e : ∀ X, F.obj X ≅ Gobj X) : EnrichedFunctor V C I where
  obj := Gobj
  map X Y := F.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom
  map_id X := by
    rw [F.map_id_assoc]
    exact Iso.eId_comp_eHomCongr V (e X)
  map_comp X Y Z := by
    rw [F.map_comp_assoc]
    rw [clientECompCompEHomCongr]
    rw [← tensorHom_comp_tensorHom_assoc]

omit [MonoidalCategory I] in
private theorem clientRawMapEqConjugateMap
    {C : Type uC} [EnrichedCategory V C]
    (F : EnrichedFunctor V C I) (Gobj : C → I)
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
  apply clientMapEqCompEHomCongr (a := e X) (b := e Y)
  exact unitGradedNaturality_eq_whisker
    (F.map X Y) (s X Y) (e X).hom (e Y).hom (hnat X Y)

omit [MonoidalCategory I] in
private def clientRawConjugateEnrichedFunctor
    {C : Type uC} [EnrichedCategory V C]
    (F : EnrichedFunctor V C I) (Gobj : C → I)
    (s : ∀ X Y : C, (X ⟶[V] Y) ⟶ (Gobj X ⟶[V] Gobj Y))
    (e : ∀ X, F.obj X ≅ Gobj X)
    (hnat : ∀ X Y,
      (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
            (F.map X Y ⊗ₘ eHomEquiv V (e Y).hom) ≫
          eComp V (F.obj X) (F.obj Y) (Gobj Y) =
        (eHomEquiv V (e X).hom ⊗ₘ s X Y) ≫
          eComp V (F.obj X) (Gobj X) (Gobj Y)) :
    EnrichedFunctor V C I := by
  let G := clientConjugateEnrichedFunctor F Gobj e
  refine
    { obj := Gobj
      map := s
      map_id := ?_
      map_comp := ?_ }
  · intro X
    rw [clientRawMapEqConjugateMap F Gobj s e hnat]
    exact G.map_id X
  · intro X Y Z
    rw [clientRawMapEqConjugateMap F Gobj s e hnat]
    rw [clientRawMapEqConjugateMap F Gobj s e hnat]
    rw [clientRawMapEqConjugateMap F Gobj s e hnat]
    exact G.map_comp X Y Z

section BraidedClients

variable [BraidedCategory I]
variable {d : EnrichedMonoidalCategoryData V I}
variable (b : EnrichedBraidedMonoidalCategoryData V I d)

private def clientSwappedTensor : EnrichedFunctor V (I × I) I :=
  clientRawConjugateEnrichedFunctor d.tensorEnrichedFunctor
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

example : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    d.tensorEnrichedFunctor (clientSwappedTensor b) :=
  b.braidingGraded

example : d.tensorEnrichedFunctor ≅ clientSwappedTensor b :=
  b.braidingIso

example (X : I × I) :
    eId V X ≫ (clientSwappedTensor b).map X X =
      eId V ((clientSwappedTensor b).obj X) :=
  (clientSwappedTensor b).map_id X

example (X Y Z : I × I) :
    eComp V X Y Z ≫ (clientSwappedTensor b).map X Z =
      ((clientSwappedTensor b).map X Y ⊗ₘ
        (clientSwappedTensor b).map Y Z) ≫
      eComp V ((clientSwappedTensor b).obj X)
        ((clientSwappedTensor b).obj Y)
        ((clientSwappedTensor b).obj Z) :=
  (clientSwappedTensor b).map_comp X Y Z

end BraidedClients

end PublicEndpointClients

section ProductEnrichment

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable (C : Type uC) [EnrichedCategory V C]
variable (D : Type uD) [EnrichedCategory V D]

attribute [local instance] Enriched.prodCategory

example (X : C × D) :
    eId V X =
      (λ_ (𝟙_ V)).inv ≫ (eId V X.1 ⊗ₘ eId V X.2) :=
  Enriched.prodEId V C D X

example (X Y Z : C × D) :
    eComp V X Y Z =
      MonoidalCategory.tensorμ
          (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)
          (Y.1 ⟶[V] Z.1) (Y.2 ⟶[V] Z.2) ≫
        (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2) :=
  Enriched.prodEComp V C D X Y Z

example (X Y : C × D) :
    (λ_ (X ⟶[V] Y)).inv ≫ eId V X ▷ (X ⟶[V] Y) ≫
        eComp V X X Y =
      𝟙 (X ⟶[V] Y) :=
  e_id_comp V X Y

example (X Y : C × D) :
    (ρ_ (X ⟶[V] Y)).inv ≫ (X ⟶[V] Y) ◁ eId V Y ≫
        eComp V X Y Y =
      𝟙 (X ⟶[V] Y) :=
  e_comp_id V X Y

example (W X Y Z : C × D) :
    (α_ (W ⟶[V] X) (X ⟶[V] Y) (Y ⟶[V] Z)).inv ≫
          eComp V W X Y ▷ (Y ⟶[V] Z) ≫ eComp V W Y Z =
      (W ⟶[V] X) ◁ eComp V X Y Z ≫ eComp V W X Z :=
  e_assoc V W X Y Z

end ProductEnrichment

section NoProductOrdinaryInference

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable (C : Type uC) [Category.{vC} C]
  [EnrichedOrdinaryCategory V C]
variable (D : Type uD) [Category.{vD} D]
  [EnrichedOrdinaryCategory V D]

attribute [local instance] Enriched.prodCategory

example : True := by
  fail_if_success
    exact (inferInstance : EnrichedOrdinaryCategory V (C × D))
  trivial

end NoProductOrdinaryInference

section MonoidalData

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable (I : Type uI) [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
variable (d : EnrichedMonoidalCategoryData V I)

attribute [local instance] Enriched.prodCategory

example (i j : I) :
    (Enriched.prodCategory V I I).id (i, j) ≫
        d.tensorMap i i j j =
      eId V (i ⊗ j) :=
  d.tensorMap_id i j

#check EnrichedMonoidalCategoryData.tensorMap_comp
#check EnrichedMonoidalCategoryData.tensorMap_eHomEquiv
#check EnrichedMonoidalCategoryData.associatorNaturality
#check EnrichedMonoidalCategoryData.leftUnitorNaturality
#check EnrichedMonoidalCategoryData.rightUnitorNaturality

example (i i' i'' j j' j'' : I) :=
  d.tensorMap_comp i i' i'' j j' j''

example {i i' j j' : I} (f : i ⟶ i') (g : j ⟶ j') :=
  d.tensorMap_eHomEquiv f g

example (i i' j j' k k' : I) :=
  d.associatorNaturality i i' j j' k k'

example (i i' : I) :=
  d.leftUnitorNaturality i i'

example (i i' : I) :=
  d.rightUnitorNaturality i i'

example (X : (I × I) × I) :
    d.associatorGraded.app X =
      eHomEquiv V (α_ X.1.1 X.1.2 X.2).hom :=
  d.associatorGraded_app X

example (X : I) :
    d.leftUnitorGraded.app X = eHomEquiv V (λ_ X).hom :=
  d.leftUnitorGraded_app X

example (X : I) :
    d.rightUnitorGraded.app X = eHomEquiv V (ρ_ X).hom :=
  d.rightUnitorGraded_app X

#check EnrichedMonoidalCategoryData.associatorGraded
#check EnrichedMonoidalCategoryData.associatorIso
#check EnrichedMonoidalCategoryData.leftUnitorGraded
#check EnrichedMonoidalCategoryData.leftUnitorIso
#check EnrichedMonoidalCategoryData.rightUnitorGraded
#check EnrichedMonoidalCategoryData.rightUnitorIso

example (W X Y Z : I) :
    eHomEquiv V (((α_ W X Y).hom ▷ Z) ≫
          (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom) =
      eHomEquiv V ((α_ (W ⊗ X) Y Z).hom ≫
        (α_ W X (Y ⊗ Z)).hom) :=
  d.pentagon W X Y Z

example (X Y : I) :
    eHomEquiv V ((α_ X (𝟙_ I) Y).hom ≫ X ◁ (λ_ Y).hom) =
      eHomEquiv V ((ρ_ X).hom ▷ Y) :=
  d.triangle X Y

example : True := by
  fail_if_success
    exact (inferInstance : EnrichedMonoidalCategoryData V I)
  trivial

end MonoidalData

section BraidedData

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable (I : Type uI) [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [BraidedCategory I]
variable {d : EnrichedMonoidalCategoryData V I}
variable (b : EnrichedBraidedMonoidalCategoryData V I d)

attribute [local instance] Enriched.prodCategory

#check EnrichedBraidedMonoidalCategoryData.braidingNaturality

example (i i' j j' : I) :=
  b.braidingNaturality i i' j j'

example (X : I × I) :
    b.braidingGraded.app X = eHomEquiv V (β_ X.1 X.2).hom :=
  b.braidingGraded_app X

#check EnrichedBraidedMonoidalCategoryData.braidingGraded
#check EnrichedBraidedMonoidalCategoryData.braidingIso

example (X Y Z : I) :
    eHomEquiv V ((α_ X Y Z).hom ≫
          (β_ X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom) =
      eHomEquiv V (((β_ X Y).hom ▷ Z) ≫
        (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom) :=
  b.hexagonForward X Y Z

example (X Y Z : I) :
    eHomEquiv V ((α_ X Y Z).inv ≫
          (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv) =
      eHomEquiv V ((X ◁ (β_ Y Z).hom) ≫
        (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y) :=
  b.hexagonReverse X Y Z

end BraidedData

section SymmetricData

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable (I : Type uI) [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [SymmetricCategory I]
variable {d : EnrichedMonoidalCategoryData V I}
variable (b : EnrichedSymmetricMonoidalCategoryData V I d)

example (X Y : I) :
    eHomEquiv V ((β_ X Y).hom ≫ (β_ Y X).hom) =
      eId V (X ⊗ Y) :=
  b.symmetry X Y

end SymmetricData

section NaturalTransformationConversions

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable {C : Type uC} [Category.{vC} C]
  [EnrichedOrdinaryCategory V C]
variable {D : Type uD} [Category.{vD} D]
  [EnrichedOrdinaryCategory V D]
variable {F G : EnrichedFunctor V C D}

example (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) :
    EnrichedNatTrans F G :=
  a.toEnrichedNatTrans

example (hsep : IsSeparator (𝟙_ V)) (a : EnrichedNatTrans F G) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G :=
  a.toGradedNatTrans hsep

example (_a : EnrichedNatTrans F G) : True := by
  fail_if_success
    exact (_a.toGradedNatTrans :
      GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)
  trivial

end NaturalTransformationConversions

section ClosedSelf

open scoped MonoidalClosed

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]

example (X X' Y Y' : V) :
    MonoidalClosed.uncurry
        ((MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
          X X' Y Y') =
      MonoidalCategory.tensorμ X Y
          ((ihom X).obj X') ((ihom Y).obj Y') ≫
        ((ihom.ev X).app X' ⊗ₘ (ihom.ev Y).app Y') := by
  rw [MonoidalClosed.enrichedMonoidalCategoryDataSelf_tensorMap]
  exact MonoidalClosed.uncurry_curry _

end ClosedSelf

section ExternalTensor

open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {C : Type uC} [EnrichedCategory V C]
variable {D : Type uD} [EnrichedCategory V D]
variable (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)

attribute [local instance] Enriched.prodCategory

example (X : C × D) :
    (EnrichedFunctor.externalTensor F G).obj X =
      F.obj X.1 ⊗ G.obj X.2 :=
  EnrichedFunctor.externalTensor_obj F G X

example (X Y : C × D) :
    (EnrichedFunctor.externalTensor F G).map X Y =
      (F.map X.1 Y.1 ⊗ₘ G.map X.2 Y.2) ≫
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
          (F.obj X.1) (F.obj Y.1) (G.obj X.2) (G.obj Y.2) :=
  EnrichedFunctor.externalTensor_map F G X Y

end ExternalTensor

section UniverseClients

variable (V₁ : Type 1) [Category.{1} V₁] [MonoidalCategory V₁]
  [BraidedCategory V₁]
variable (I₁ : Type 1) [Category.{1} I₁] [MonoidalCategory I₁]
  [EnrichedOrdinaryCategory V₁ I₁]

#check EnrichedMonoidalCategoryData V₁ I₁

variable (V₀ : Type) [Category.{0} V₀] [MonoidalCategory V₀]
  [BraidedCategory V₀]
variable (I₀ : Type) [Category.{0} I₀] [MonoidalCategory I₀]
  [EnrichedOrdinaryCategory V₀ I₀]

#check EnrichedMonoidalCategoryData V₀ I₀

end UniverseClients

end CategoryTheory

#print axioms CategoryTheory.Enriched.prodCategory
#print axioms CategoryTheory.EnrichedMonoidalCategoryData.tensorEnrichedFunctor
#print axioms CategoryTheory.EnrichedMonoidalCategoryData.associatorIso
#print axioms CategoryTheory.EnrichedBraidedMonoidalCategoryData.braidingIso
#print axioms CategoryTheory.MonoidalClosed.enrichedMonoidalCategoryDataSelf
#print axioms CategoryTheory.EnrichedFunctor.externalTensor
