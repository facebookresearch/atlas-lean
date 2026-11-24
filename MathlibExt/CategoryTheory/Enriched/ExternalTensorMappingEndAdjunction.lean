/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.WeightedEndVariance
public import MathlibExt.CategoryTheory.Enriched.GradingConvention
public import MathlibExt.CategoryTheory.Enriched.Monoidal.ExternalTensor
public import MathlibExt.CategoryTheory.Enriched.Restriction
public import MathlibExt.CategoryTheory.Enriched.FunctorCategoryIso
public import MathlibExt.CategoryTheory.Enriched.GradedTensor
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorHom
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ScalarComparison
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingCoherence

/-!
# External tensors and their actual parameterized weighted ends

For independent plain enriched types `A` and `B`, external tensoring by `F`
is left adjoint to the functor whose value at `b` is the actual weighted end
of `F` and the original `b`-slice of the target. Slices insert the enriched
identity in the fixed factor. Naturality acts on both entire product Hom
objects, and the end retains its original products, equalizer and projections.

The correspondence is natural in every ambient coefficient through its
canonical center grade, in both input diagrams and in the target. Its
tensor-unit case gives the ordinary unit, counit and both triangle identities.
The scalar/grade correspondence is the canonical `GradedTensor` construction.
Restriction along an original enriched tensor retains the literal
`fixedRightTensor` slice, including its full identity insertion and tensor map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uA uB vI

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.ExternalTensorMappingEndAdjunction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

attribute [local instance] Enriched.prodCategory

/-- Insert the fixed parameter through its entire enriched identity. -/
def fixedRightPair (b : B) : EnrichedFunctor V A (A × B) where
  obj a := (a, b)
  map a a' := (ρ_ (a ⟶[V] a')).inv ≫
    (𝟙 (a ⟶[V] a') ⊗ₘ eId V b)
  map_id a := by
    change eId V a ≫ (ρ_ (a ⟶[V] a)).inv ≫
        (𝟙 (a ⟶[V] a) ⊗ₘ eId V b) =
      (λ_ (𝟙_ V)).inv ≫ (eId V a ⊗ₘ eId V b)
    rw [rightUnitor_inv_naturality_assoc, unitors_inv_equal]
    slice_lhs 2 3 =>
      rw [← tensorHom_id, tensorHom_comp_tensorHom]
      simp
  map_comp a a' a'' := by
    have hIdentity : (eId V b ⊗ₘ eId V b) ≫ eComp V b b b =
        (λ_ (𝟙_ V)).hom ≫ eId V b := by
      rw [← cancel_epi (λ_ (𝟙_ V)).inv]
      simp only [Iso.inv_hom_id_assoc]
      rw [leftUnitor_inv_comp_tensorHom_assoc]
      rw [e_id_comp, Category.comp_id]
    have hTensorUnit {X Y Z : V} (f : X ⟶ Y) (g : 𝟙_ V ⟶ Z) :
        f ⊗ₘ g = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv ≫ Y ◁ g := by
      rw [← cancel_epi (ρ_ X).inv]
      simp only [Iso.inv_hom_id_assoc]
      exact rightUnitor_inv_comp_tensorHom f g
    change eComp V a a' a'' ≫ (ρ_ (a ⟶[V] a'')).inv ≫
        (𝟙 (a ⟶[V] a'') ⊗ₘ eId V b) =
      (((ρ_ (a ⟶[V] a')).inv ≫
          (𝟙 (a ⟶[V] a') ⊗ₘ eId V b)) ⊗ₘ
        ((ρ_ (a' ⟶[V] a'')).inv ≫
          (𝟙 (a' ⟶[V] a'') ⊗ₘ eId V b))) ≫
        MonoidalCategory.tensorμ (a ⟶[V] a') (b ⟶[V] b)
          (a' ⟶[V] a'') (b ⟶[V] b) ≫
        (eComp V a a' a'' ⊗ₘ eComp V b b b)
    rw [← cancel_epi (ρ_ ((a ⟶[V] a') ⊗ (a' ⟶[V] a''))).hom]
    nth_rewrite 2 [MonoidalCategory.tensor_right_unitality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [MonoidalCategory.tensorμ_natural_assoc, tensorHom_comp_tensorHom]
    simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rw [hIdentity]
    nth_rewrite 2 [← Category.id_comp (eComp V a a' a'')]
    rw [← tensorHom_comp_tensorHom]
    simp only [id_tensorHom]
    rw [hTensorUnit, ← MonoidalCategory.rightUnitor_monoidal_assoc,
      ← MonoidalCategory.tensor_right_unitality_assoc]

/-- The original slice of a product-enriched diagram at the chosen parameter. -/
def slice (Y : EnrichedFunctorCat V (A × B)) (b : B) : EnrichedFunctorCat V A :=
  ⟨(fixedRightPair (V := V) (A := A) b).comp V Y.toEnrichedFunctor⟩

/-- The slice retains the original object. -/
@[simp]
theorem slice_obj (Y : EnrichedFunctorCat V (A × B)) (b : B) (a : A) :
    (slice Y b).toEnrichedFunctor.obj a = Y.toEnrichedFunctor.obj (a, b) := rfl

/-- The entire slice Hom inserts the original enriched identity in the fixed factor. -/
theorem slice_map (Y : EnrichedFunctorCat V (A × B)) (b : B) (a a' : A) :
    (slice Y b).toEnrichedFunctor.map a a' =
      (ρ_ (a ⟶[V] a')).inv ≫ (𝟙 (a ⟶[V] a') ⊗ₘ eId V b) ≫
        Y.toEnrichedFunctor.map (a, b) (a', b) := by
  exact Category.assoc _ _ _

/-- External tensoring by the fixed original weight acts on genuine transformations. -/
def leftFunctor (F : EnrichedFunctorCat V A) :
    EnrichedFunctorCat V B ⥤ EnrichedFunctorCat V (A × B) where
  obj X := ⟨F.toEnrichedFunctor.externalTensor X.toEnrichedFunctor⟩
  map f := EnrichedFunctor.externalMap (𝟙 F) f
  map_id X := EnrichedFunctor.externalMap_id F.toEnrichedFunctor X.toEnrichedFunctor
  map_comp f g := by
    have h := EnrichedFunctor.externalMap_comp (𝟙 F) (𝟙 F) f g
    have hF : GradedNatTrans.unitComp (𝟙 F) (𝟙 F) = (𝟙 F) :=
      @Category.id_comp (EnrichedFunctorCat V A) _ F F (𝟙 F)
    rw [hF] at h
    exact h

/-- The complete left-functor component tensors the original second-factor map. -/
theorem leftFunctor_map_component (F : EnrichedFunctorCat V A)
    {X X' : EnrichedFunctorCat V B} (f : X ⟶ X') (a : A) (b : B) :
    component ((leftFunctor F).map f) (a, b) =
      𝟙 (F.toEnrichedFunctor.obj a) ⊗ₘ component f b := by
  change (eHomEquiv V).symm ((EnrichedFunctor.externalMap (𝟙 F) f).app (a, b)) =
    𝟙 (F.toEnrichedFunctor.obj a) ⊗ₘ (eHomEquiv V).symm (f.app b)
  rw [EnrichedFunctor.externalMap_component]
  exact congrArg (fun z => z ⊗ₘ component f b) (component_id F a)


/-- The full fixed-first enriched pair insertion. -/
def fixedLeftPair (a0 : A) : EnrichedFunctor V B (A × B) where
  obj b := (a0, b)
  map b b' := (λ_ (b ⟶[V] b')).inv ≫
    (eId V a0 ⊗ₘ 𝟙 (b ⟶[V] b'))
  map_id b := by
    change eId V b ≫ (λ_ (b ⟶[V] b)).inv ≫
        (eId V a0 ⊗ₘ 𝟙 (b ⟶[V] b)) =
      (λ_ (𝟙_ V)).inv ≫ (eId V a0 ⊗ₘ eId V b)
    rw [leftUnitor_inv_naturality_assoc]
    slice_lhs 2 3 =>
      rw [← id_tensorHom, tensorHom_comp_tensorHom]
      simp
  map_comp b b' b'' := by
    have hIdentity : (eId V a0 ⊗ₘ eId V a0) ≫ eComp V a0 a0 a0 =
        (λ_ (𝟙_ V)).hom ≫ eId V a0 := by
      rw [← cancel_epi (λ_ (𝟙_ V)).inv]
      simp only [Iso.inv_hom_id_assoc]
      rw [leftUnitor_inv_comp_tensorHom_assoc, e_id_comp, Category.comp_id]
    have hTensorUnit {X Y Z : V} (f : 𝟙_ V ⟶ Y) (g : X ⟶ Z) :
        f ⊗ₘ g = (λ_ X).hom ≫ g ≫ (λ_ Z).inv ≫ f ▷ Z := by
      rw [← cancel_epi (λ_ X).inv]
      simp only [Iso.inv_hom_id_assoc]
      exact leftUnitor_inv_comp_tensorHom f g
    change eComp V b b' b'' ≫ (λ_ (b ⟶[V] b'')).inv ≫
        (eId V a0 ⊗ₘ 𝟙 (b ⟶[V] b'')) =
      (((λ_ (b ⟶[V] b')).inv ≫ (eId V a0 ⊗ₘ 𝟙 (b ⟶[V] b'))) ⊗ₘ
        ((λ_ (b' ⟶[V] b'')).inv ≫ (eId V a0 ⊗ₘ 𝟙 (b' ⟶[V] b'')))) ≫
        MonoidalCategory.tensorμ (a0 ⟶[V] a0) (b ⟶[V] b')
          (a0 ⟶[V] a0) (b' ⟶[V] b'') ≫
        (eComp V a0 a0 a0 ⊗ₘ eComp V b b' b'')
    rw [← cancel_epi (λ_ ((b ⟶[V] b') ⊗ (b' ⟶[V] b''))).hom]
    nth_rewrite 2 [MonoidalCategory.tensor_left_unitality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [MonoidalCategory.tensorμ_natural_assoc, tensorHom_comp_tensorHom]
    simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rw [hIdentity]
    nth_rewrite 2 [← Category.id_comp (eComp V b b' b'')]
    rw [← tensorHom_comp_tensorHom]
    simp only [tensorHom_id]
    rw [hTensorUnit, ← MonoidalCategory.leftUnitor_monoidal_assoc,
      ← MonoidalCategory.tensor_left_unitality_assoc]


omit [SymmetricCategory V] [MonoidalClosed V] in
private theorem inserted_left_identity_compForProof {C : Type*} [EnrichedCategory V C] (X Y : C) :
    (eId V X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ eComp V X X Y =
      (λ_ (X ⟶[V] Y)).hom := by
  rw [← cancel_epi (λ_ (X ⟶[V] Y)).inv]
  simp only [tensorHom_id, e_id_comp,
    Iso.inv_hom_id]

omit [SymmetricCategory V] [MonoidalClosed V] in
private theorem inserted_right_identity_compForProof {C : Type*} [EnrichedCategory V C] (X Y : C) :
    (𝟙 (X ⟶[V] Y) ⊗ₘ eId V Y) ≫ eComp V X Y Y =
      (ρ_ (X ⟶[V] Y)).hom := by
  rw [← cancel_epi (ρ_ (X ⟶[V] Y)).inv]
  simp only [id_tensorHom, e_comp_id,
    Iso.inv_hom_id]

omit [MonoidalClosed V] in
/-- The full crossing left by two opposite unit insertions is positive. -/
private theorem tensor_unit_exchange_leftForProof (H B : V) :
    ((λ_ H).inv ⊗ₘ (ρ_ B).inv) ≫
      MonoidalCategory.tensorμ (𝟙_ V) H B (𝟙_ V) ≫
      ((λ_ B).hom ⊗ₘ (ρ_ H).hom) = (β_ H B).hom := by
  let X : V := H ⊗ B
  let Y : V := B ⊗ H
  let f : X ⟶ Y := (β_ H B).hom
  have hPre :
      ((λ_ H).inv ⊗ₘ (ρ_ B).inv) ≫
        (α_ (𝟙_ V) H (B ⊗ (𝟙_ V))).hom ≫
        (𝟙_ V) ◁ (α_ H B (𝟙_ V)).inv =
      (λ_ X).inv ≫ (𝟙_ V) ◁ (ρ_ X).inv := by
    dsimp only [X]
    monoidal
  have hPost :
      (𝟙_ V) ◁ (α_ B H (𝟙_ V)).hom ≫
        (α_ (𝟙_ V) B (H ⊗ (𝟙_ V))).inv ≫
        ((λ_ B).hom ⊗ₘ (ρ_ H).hom) =
      (𝟙_ V) ◁ (ρ_ Y).hom ≫ (λ_ Y).hom := by
    dsimp only [Y]
    monoidal
  have hRight :
      (ρ_ X).inv ≫ (f ▷ (𝟙_ V)) ≫ (ρ_ Y).hom = f := by
    rw [rightUnitor_naturality]
    simp only [Iso.inv_hom_id_assoc]
  have hLeft :
      (λ_ X).inv ≫ (𝟙_ V) ◁ f ≫ (λ_ Y).hom = f := by
    rw [leftUnitor_naturality]
    simp only [Iso.inv_hom_id_assoc]
  calc
    _ = (((λ_ H).inv ⊗ₘ (ρ_ B).inv) ≫
        (α_ (𝟙_ V) H (B ⊗ (𝟙_ V))).hom ≫
        (𝟙_ V) ◁ (α_ H B (𝟙_ V)).inv) ≫
      (𝟙_ V) ◁ (f ▷ (𝟙_ V)) ≫
      ((𝟙_ V) ◁ (α_ B H (𝟙_ V)).hom ≫
        (α_ (𝟙_ V) B (H ⊗ (𝟙_ V))).inv ≫
        ((λ_ B).hom ⊗ₘ (ρ_ H).hom)) := by
      simp only [MonoidalCategory.tensorμ, f, Category.assoc]
    _ = ((λ_ X).inv ≫ (𝟙_ V) ◁ (ρ_ X).inv) ≫
        (𝟙_ V) ◁ (f ▷ (𝟙_ V)) ≫
        ((𝟙_ V) ◁ (ρ_ Y).hom ≫ (λ_ Y).hom) := by
      rw [hPre, hPost]
    _ = (λ_ X).inv ≫
        (𝟙_ V) ◁ ((ρ_ X).inv ≫ (f ▷ (𝟙_ V)) ≫ (ρ_ Y).hom) ≫
        (λ_ Y).hom := by
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    _ = f := by rw [hRight]; exact hLeft
    _ = _ := rfl

omit [MonoidalClosed V] in
/-- The other product path crosses only the tensor unit. -/
private theorem tensor_unit_exchange_rightForProof (B H : V) :
    ((ρ_ B).inv ⊗ₘ (λ_ H).inv) ≫
      MonoidalCategory.tensorμ B (𝟙_ V) (𝟙_ V) H ≫
      ((ρ_ B).hom ⊗ₘ (λ_ H).hom) = 𝟙 (B ⊗ H) := by
  dsimp only [MonoidalCategory.tensorμ]
  rw [CategoryTheory.braiding_tensorUnit_left]
  monoidal


omit [MonoidalClosed V] in
/-- Both complete product-Hom paths retain the original whole Hom crossing. -/
theorem product_full_exchange (a a' : A) (b b' : B) :
    (((fixedLeftPair (V := V) a).map b b') ⊗ₘ
        (fixedRightPair (V := V) b').map a a') ≫
      (Enriched.prodCategory V A B).comp (a, b) (a, b') (a', b') =
    (β_ (b ⟶[V] b') (a ⟶[V] a')).hom ≫
      (((fixedRightPair (V := V) b).map a a') ⊗ₘ
        (fixedLeftPair (V := V) a').map b b') ≫
      (Enriched.prodCategory V A B).comp (a, b) (a', b) (a', b') := by
  let H : V := b ⟶[V] b'
  let P : V := a ⟶[V] a'
  have hL :
      (((fixedLeftPair (V := V) a).map b b') ⊗ₘ
          (fixedRightPair (V := V) b').map a a') ≫
        (Enriched.prodCategory V A B).comp (a, b) (a, b') (a', b') =
      (β_ H P).hom := by
    dsimp only [fixedLeftPair, fixedRightPair]
    rw [Enriched.prodEComp]
    rw [← tensorHom_comp_tensorHom_assoc, MonoidalCategory.tensorμ_natural_assoc,
      tensorHom_comp_tensorHom]
    simp only [tensorHom_id, id_tensorHom]
    have hB : (eId V a ▷ P) ≫ eComp V a a a' = (λ_ P).hom := by
      simpa only [P, tensorHom_id] using
        inserted_left_identity_compForProof (V := V) a a'
    have hH : (H ◁ eId V b') ≫ eComp V b b' b' = (ρ_ H).hom := by
      simpa only [H, id_tensorHom] using
        inserted_right_identity_compForProof (V := V) b b'
    rw [hB, hH]
    exact tensor_unit_exchange_leftForProof H P
  have hR :
      (((fixedRightPair (V := V) b).map a a') ⊗ₘ
          (fixedLeftPair (V := V) a').map b b') ≫
        (Enriched.prodCategory V A B).comp (a, b) (a', b) (a', b') =
      𝟙 (P ⊗ H) := by
    dsimp only [fixedLeftPair, fixedRightPair]
    rw [Enriched.prodEComp]
    rw [← tensorHom_comp_tensorHom_assoc, MonoidalCategory.tensorμ_natural_assoc,
      tensorHom_comp_tensorHom]
    simp only [tensorHom_id, id_tensorHom]
    have hB : (P ◁ eId V a') ≫ eComp V a a' a' = (ρ_ P).hom := by
      simpa only [P, id_tensorHom] using
        inserted_right_identity_compForProof (V := V) a a'
    have hH : (eId V b ▷ H) ≫ eComp V b b b' = (λ_ H).hom := by
      simpa only [H, tensorHom_id] using
        inserted_left_identity_compForProof (V := V) b b'
    rw [hB, hH]
    exact tensor_unit_exchange_rightForProof P H
  rw [hL]
  change (β_ H P).hom = (β_ H P).hom ≫ _
  rw [hR, Category.comp_id]



set_option backward.isDefEq.respectTransparency false in
/-- The complete parameter Hom acts on every original slice component. -/
def parameterGrade (Y : EnrichedFunctorCat V (A × B)) (b b' : B) :
    GradedNatTrans ((Center.ofBraided V).obj (b ⟶[V] b'))
      (slice Y b).toEnrichedFunctor (slice Y b').toEnrichedFunctor where
  app a := (fixedLeftPair (V := V) (B := B) a).map b b' ≫
    Y.toEnrichedFunctor.map (a, b) (a, b')
  naturality a a' := by
    dsimp only [Center.ofBraided, Center.ofBraidedObj]
    have h := congrArg
      (fun q => q ≫ Y.toEnrichedFunctor.map (a, b) (a', b'))
      (product_full_exchange (V := V) a a' b b')
    let p := (fixedLeftPair (V := V) (B := B) a).map b b'
    let q := (fixedRightPair (V := V) (A := A) b').map a a'
    let r := (fixedRightPair (V := V) (A := A) b).map a a'
    let s := (fixedLeftPair (V := V) (B := B) a').map b b'
    have hL := congrArg (fun z => (p ⊗ₘ q) ≫ z)
      (Y.toEnrichedFunctor.map_comp (a, b) (a, b') (a', b')).symm
    have hR := congrArg (fun z => (β_ (b ⟶[V] b') (a ⟶[V] a')).hom ≫
      (r ⊗ₘ s) ≫ z)
      (Y.toEnrichedFunctor.map_comp (a, b) (a', b) (a', b')).symm
    have h' : (p ⊗ₘ q) ≫ eComp V (a, b) (a, b') (a', b') ≫
        Y.toEnrichedFunctor.map (a, b) (a', b') =
      (β_ (b ⟶[V] b') (a ⟶[V] a')).hom ≫ (r ⊗ₘ s) ≫
        eComp V (a, b) (a', b) (a', b') ≫
        Y.toEnrichedFunctor.map (a, b) (a', b') := by
      simpa only [p, q, r, s, Category.assoc, eComp] using h
    have hh := hL.trans (h'.trans hR.symm)
    simpa only [p, q, r, s, slice_map, slice_obj, fixedRightPair,
      tensorHom_comp_tensorHom_assoc, Category.assoc] using hh.symm



omit [MonoidalClosed V] in
/-- The right-then-left product path is the identity on the entire product Hom. -/
theorem product_factorization (a a' : A) (b b' : B) :
    (((fixedRightPair (V := V) b).map a a') ⊗ₘ
        (fixedLeftPair (V := V) a').map b b') ≫
      (Enriched.prodCategory V A B).comp (a, b) (a', b) (a', b') =
        𝟙 ((a ⟶[V] a') ⊗ (b ⟶[V] b')) := by
  dsimp only [fixedLeftPair, fixedRightPair]
  rw [Enriched.prodEComp]
  rw [← tensorHom_comp_tensorHom_assoc, MonoidalCategory.tensorμ_natural_assoc,
    tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  have hA : ((a ⟶[V] a') ◁ eId V a') ≫ eComp V a a' a' =
      (ρ_ (a ⟶[V] a')).hom := by
    simpa only [id_tensorHom] using inserted_right_identity_compForProof (V := V) a a'
  have hB : (eId V b ▷ (b ⟶[V] b')) ≫ eComp V b b b' =
      (λ_ (b ⟶[V] b')).hom := by
    simpa only [tensorHom_id] using inserted_left_identity_compForProof (V := V) b b'
  rw [hA, hB]
  exact tensor_unit_exchange_rightForProof (a ⟶[V] a') (b ⟶[V] b')

omit [SymmetricCategory V] in
private theorem action_identity {C : Type*} [EnrichedCategory V C]
    (F : EnrichedFunctor V C V) (a : C) :
    F.obj a ◁ eId V a ≫ MonoidalClosed.uncurry (F.map a a) =
      (ρ_ (F.obj a)).hom := by
  have h := congrArg MonoidalClosed.uncurry (F.map_id a)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at h
  exact h

omit [MonoidalClosed V] in
private theorem tensor_action_fixedRight {U U' K P Q : V}
    (f : U ⊗ P ⟶ U') (g : K ⊗ Q ⟶ K) (q : 𝟙_ V ⟶ Q)
    (hg : K ◁ q ≫ g = (ρ_ K).hom) :
    (U ⊗ K) ◁ ((ρ_ P).inv ≫ (𝟙 P ⊗ₘ q)) ≫
        tensorμ U K P Q ≫ (f ⊗ₘ g) =
      (α_ U K P).hom ≫ U ◁ (β_ K P).hom ≫
        (α_ U P K).inv ≫ (f ⊗ₘ 𝟙 K) := by
  rw [whiskerLeft_comp, Category.assoc, tensorμ_natural_right_assoc,
    tensorHom_comp_tensorHom, whiskerLeft_id, Category.id_comp, hg]
  dsimp only [tensorμ]
  monoidal

omit [MonoidalClosed V] in
private theorem tensor_action_fixedLeft {U K K' P Q : V}
    (f : U ⊗ P ⟶ U) (g : K ⊗ Q ⟶ K') (q : 𝟙_ V ⟶ P)
    (hf : U ◁ q ≫ f = (ρ_ U).hom) :
    (U ⊗ K) ◁ ((λ_ Q).inv ≫ (q ⊗ₘ 𝟙 Q)) ≫
        tensorμ U K P Q ≫ (f ⊗ₘ g) =
      (α_ U K Q).hom ≫ U ◁ g := by
  rw [whiskerLeft_comp, Category.assoc, tensorμ_natural_right_assoc,
    tensorHom_comp_tensorHom, whiskerLeft_id, Category.id_comp, hf]
  dsimp only [tensorμ]
  rw [braiding_tensorUnit_right]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Fixing the second factor contracts its genuine identity in the whole external action. -/
theorem external_rightSlice_action (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (b : B) (a a' : A) :
    MonoidalClosed.uncurry
        ((slice ((leftFunctor F).obj X) b).toEnrichedFunctor.map a a') =
      (α_ (F.toEnrichedFunctor.obj a) (X.toEnrichedFunctor.obj b) (a ⟶[V] a')).hom ≫
        F.toEnrichedFunctor.obj a ◁ (β_ (X.toEnrichedFunctor.obj b) (a ⟶[V] a')).hom ≫
        (α_ (F.toEnrichedFunctor.obj a) (a ⟶[V] a') (X.toEnrichedFunctor.obj b)).inv ≫
        (MonoidalClosed.uncurry (F.toEnrichedFunctor.map a a') ⊗ₘ
          𝟙 (X.toEnrichedFunctor.obj b)) := by
  change MonoidalClosed.uncurry ((fixedRightPair (V := V) b).map a a' ≫
    (F.toEnrichedFunctor.externalTensor X.toEnrichedFunctor).map (a, b) (a', b)) = _
  rw [MonoidalClosed.uncurry_natural_left, EnrichedFunctor.externalTensor_uncurry]
  exact tensor_action_fixedRight _ _ (eId V b) (action_identity X.toEnrichedFunctor b)

set_option backward.isDefEq.respectTransparency false in
/-- Fixing the first factor retains the complete scalar-tensor action in the second factor. -/
theorem external_leftSlice_action (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (a : A) (b b' : B) :
    MonoidalClosed.uncurry (((fixedLeftPair (V := V) a).comp V
        (F.toEnrichedFunctor.externalTensor X.toEnrichedFunctor)).map b b') =
      (α_ (F.toEnrichedFunctor.obj a) (X.toEnrichedFunctor.obj b) (b ⟶[V] b')).hom ≫
        F.toEnrichedFunctor.obj a ◁ MonoidalClosed.uncurry (X.toEnrichedFunctor.map b b') := by
  change MonoidalClosed.uncurry ((fixedLeftPair (V := V) a).map b b' ≫
    (F.toEnrichedFunctor.externalTensor X.toEnrichedFunctor).map (a, b) (a, b')) = _
  rw [MonoidalClosed.uncurry_natural_left, EnrichedFunctor.externalTensor_uncurry]
  exact tensor_action_fixedLeft _ _ (eId V a) (action_identity F.toEnrichedFunctor a)

omit [MonoidalClosed V] in
private theorem tensor_action_braiding {U U' K P : V} (f : U ⊗ P ⟶ U') :
    (α_ K U P).hom ≫ K ◁ f ≫ (β_ K U').hom =
      ((β_ K U).hom ▷ P) ≫ (α_ U K P).hom ≫ U ◁ (β_ K P).hom ≫
        (α_ U P K).inv ≫ (f ⊗ₘ 𝟙 K) := by
  rw [braiding_naturality_right, braiding_tensor_right_hom, tensorHom_id]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The full original slice is isomorphic to the scalar tensor through its actual braiding. -/
def scalarSliceIso (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B) (b : B) :
    tensorLeftObject (X.toEnrichedFunctor.obj b) F ≅ slice ((leftFunctor F).obj X) b :=
  isoOfComponents _ _ (fun a => β_ (X.toEnrichedFunctor.obj b) (F.toEnrichedFunctor.obj a))
    (by
      intro a a'
      rw [tensorLeftObject_map_uncurry, external_rightSlice_action, tensorHom_id, Category.assoc]
      exact tensor_action_braiding (V := V)
        (K := X.toEnrichedFunctor.obj b)
        (MonoidalClosed.uncurry (F.toEnrichedFunctor.map a a')))

/-- The slice comparison uses the original whole braiding component. -/
theorem scalarSliceIso_hom_component (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (b : B) (a : A) :
    component (scalarSliceIso F X b).hom a =
      (β_ (X.toEnrichedFunctor.obj b) (F.toEnrichedFunctor.obj a)).hom := by
  exact isoOfComponents_hom_component _ _ _ _ a

/-- The inverse slice comparison uses the original whole inverse braiding component. -/
theorem scalarSliceIso_inv_component (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (b : B) (a : A) :
    component (scalarSliceIso F X b).inv a =
      (β_ (X.toEnrichedFunctor.obj b) (F.toEnrichedFunctor.obj a)).inv := by
  exact isoOfComponents_inv_component _ _ _ _ a

set_option backward.isDefEq.respectTransparency false in
/-- Every original full product map factors through the two original fixed-factor Hom maps. -/
theorem product_map_factorization (Y : EnrichedFunctorCat V (A × B))
    (a a' : A) (b b' : B) :
    Y.toEnrichedFunctor.map (a, b) (a', b') =
      ((slice Y b).toEnrichedFunctor.map a a' ⊗ₘ
        ((fixedLeftPair (V := V) a').comp V Y.toEnrichedFunctor).map b b') ≫
        eComp V (Y.toEnrichedFunctor.obj (a, b)) (Y.toEnrichedFunctor.obj (a', b))
          (Y.toEnrichedFunctor.obj (a', b')) := by
  let r := (fixedRightPair (V := V) (A := A) b).map a a'
  let s := (fixedLeftPair (V := V) (B := B) a').map b b'
  have hf : (r ⊗ₘ s) ≫ eComp V (a, b) (a', b) (a', b') =
      𝟙 ((a ⟶[V] a') ⊗ (b ⟶[V] b')) := product_factorization a a' b b'
  calc
    _ = (r ⊗ₘ s) ≫ eComp V (a, b) (a', b) (a', b') ≫
        Y.toEnrichedFunctor.map (a, b) (a', b') := by
      rw [← Category.assoc, hf, Category.id_comp]
    _ = ((r ≫ Y.toEnrichedFunctor.map (a, b) (a', b)) ⊗ₘ
        (s ≫ Y.toEnrichedFunctor.map (a', b) (a', b'))) ≫
        eComp V (Y.toEnrichedFunctor.obj (a, b)) (Y.toEnrichedFunctor.obj (a', b))
          (Y.toEnrichedFunctor.obj (a', b')) := by
      rw [Y.toEnrichedFunctor.map_comp, ← tensorHom_comp_tensorHom_assoc]
    _ = _ := rfl

omit [SymmetricCategory V] in
private theorem action_composition_natural {U U' K K' W W' P Q : V}
    (f : P ⟶ (ihom U).obj K) (g : Q ⟶ (ihom K).obj W)
    (f' : P ⟶ (ihom U').obj K') (g' : Q ⟶ (ihom K').obj W')
    (qU : U ⟶ U') (qK : K ⟶ K') (qW : W ⟶ W')
    (hf : MonoidalClosed.uncurry f ≫ qK =
      (qU ▷ P) ≫ MonoidalClosed.uncurry f')
    (hg : MonoidalClosed.uncurry g ≫ qW =
      (qK ▷ Q) ≫ MonoidalClosed.uncurry g') :
    MonoidalClosed.uncurry ((f ⊗ₘ g) ≫ eComp V U K W) ≫ qW =
      (qU ▷ (P ⊗ Q)) ≫ MonoidalClosed.uncurry ((f' ⊗ₘ g') ≫ eComp V U' K' W') := by
  rw [MonoidalClosed.uncurry_eComp, MonoidalClosed.uncurry_eComp]
  simp only [Category.assoc]
  rw [hg, ← comp_whiskerRight_assoc, hf, comp_whiskerRight]
  simp only [Category.assoc]
  rw [← associator_inv_naturality_left_assoc]

/-- Full naturality in the two original factors implies full product-Hom naturality. -/
theorem product_naturality_of_slices (Y Z : EnrichedFunctorCat V (A × B))
    (q : ∀ p : A × B, Y.toEnrichedFunctor.obj p ⟶ Z.toEnrichedFunctor.obj p)
    (hA : ∀ a a' b, MonoidalClosed.uncurry ((slice Y b).toEnrichedFunctor.map a a') ≫
      q (a', b) = (q (a, b) ▷ (a ⟶[V] a')) ≫
        MonoidalClosed.uncurry ((slice Z b).toEnrichedFunctor.map a a'))
    (hB : ∀ a b b', MonoidalClosed.uncurry (((fixedLeftPair (V := V) a).comp V
        Y.toEnrichedFunctor).map b b') ≫ q (a, b') =
      (q (a, b) ▷ (b ⟶[V] b')) ≫ MonoidalClosed.uncurry
        (((fixedLeftPair (V := V) a).comp V Z.toEnrichedFunctor).map b b'))
    (p p' : A × B) :
    MonoidalClosed.uncurry (Y.toEnrichedFunctor.map p p') ≫ q p' =
      (q p ⊗ₘ 𝟙 (p ⟶[V] p')) ≫ MonoidalClosed.uncurry (Z.toEnrichedFunctor.map p p') := by
  rcases p with ⟨a, b⟩
  rcases p' with ⟨a', b'⟩
  rw [product_map_factorization Y, product_map_factorization Z, tensorHom_id]
  exact action_composition_natural _ _ _ _ (q (a, b)) (q (a', b)) (q (a', b'))
    (hA a a' b) (hB a' b b')


/-!
The identity, composition, and enrichment laws below are adapted from
`MathlibExt/Topology/Category/PointedCGWH/EnrichedFunctorCategory.lean`,
credited to @toskua and Avocado, and generalized to independent enriched
index universes and an arbitrary symmetric monoidal closed base.
-/

namespace EndEnrichment

variable [HasProducts.{uA} V] [HasEqualizers V]
attribute [local instance] MonoidalClosed.enrichedCategorySelf

omit [SymmetricCategory V] [HasProducts.{uA} V] [HasEqualizers V] in
private theorem closedLeftIdentity (X Y : V) :
    (λ_ ((ihom X).obj Y)).inv ≫ eId V X ▷ (ihom X).obj Y ≫ eComp V X X Y =
      𝟙 ((ihom X).obj Y) := e_id_comp V X Y

omit [SymmetricCategory V] [HasProducts.{uA} V] [HasEqualizers V] in
private theorem closedRightIdentity (X Y : V) :
    (ρ_ ((ihom X).obj Y)).inv ≫ (ihom X).obj Y ◁ eId V Y ≫ eComp V X Y Y =
      𝟙 ((ihom X).obj Y) := e_comp_id V X Y

omit [SymmetricCategory V] [HasProducts.{uA} V] [HasEqualizers V] in
private theorem closedAssociativity (W X Y Z : V) :
    (α_ ((ihom W).obj X) ((ihom X).obj Y) ((ihom Y).obj Z)).inv ≫
        eComp V W X Y ▷ (ihom Y).obj Z ≫ eComp V W Y Z =
      (ihom W).obj X ◁ eComp V X Y Z ≫ eComp V W X Z := e_assoc V W X Y Z

/-- The actual original weighted Hom object. -/
abbrev homObject (X Y : EnrichedFunctorCat V A) : V := WeightedEndVariance.object X Y

/-- The complete original internal-Hom projection. -/
abbrev homProjection (X Y : EnrichedFunctorCat V A) (a : A) :=
  WeightedEndVariance.projection X Y a

/-- Identity is the original end lift of the actual unit-graded identity. -/
def mappingIdentity (X : EnrichedFunctorCat V A) : 𝟙_ V ⟶ homObject X X :=
  GradingConvention.endFromPositive X.toEnrichedFunctor X.toEnrichedFunctor (𝟙 X)

/-- The identity projection is the original target identity. -/
theorem mappingIdentity_π (X : EnrichedFunctorCat V A) (a : A) :
    mappingIdentity X ≫ homProjection X X a = eId V (X.toEnrichedFunctor.obj a) := by
  unfold mappingIdentity
  rw [GradingConvention.endFromPositive_symmetric_π]
  exact GradedNatTrans.unitId_app X.toEnrichedFunctor a

/-- Composition is the actual lift of the entire tensor-graded composition. -/
def mappingComposition (X Y Z : EnrichedFunctorCat V A) :
    homObject X Y ⊗ homObject Y Z ⟶ homObject X Z :=
  GradingConvention.endFromPositive X.toEnrichedFunctor Z.toEnrichedFunctor
    (GradedNatTrans.regrade
      (Functor.OplaxMonoidal.δ (Center.ofBraided V) (homObject X Y) (homObject Y Z))
      (GradedNatTrans.tensorComp
        (GradingConvention.endToPositive X.toEnrichedFunctor Y.toEnrichedFunctor
          (𝟙 (homObject X Y)))
        (GradingConvention.endToPositive Y.toEnrichedFunctor Z.toEnrichedFunctor
          (𝟙 (homObject Y Z)))))

set_option backward.isDefEq.respectTransparency false in
/-- Composition projects to the original full closed composition. -/
theorem mappingComposition_π (X Y Z : EnrichedFunctorCat V A) (a : A) :
    mappingComposition X Y Z ≫ homProjection X Z a =
      (homProjection X Y a ⊗ₘ homProjection Y Z a) ≫
        eComp V (X.toEnrichedFunctor.obj a) (Y.toEnrichedFunctor.obj a)
          (Z.toEnrichedFunctor.obj a) := by
  unfold mappingComposition
  rw [GradingConvention.endFromPositive_symmetric_π, GradedNatTrans.regrade_app,
    Center.ofBraided_δ_f]
  dsimp only [Center.ofBraided, Center.ofBraidedObj]
  rw [Category.id_comp, GradedNatTrans.tensorComp_app,
    GradingConvention.endToPositive_app_symmetric,
    GradingConvention.endToPositive_app_symmetric, Category.id_comp, Category.id_comp]

/-- The original identity is a left identity on the entire actual mapping object. -/
theorem mappingIdentity_comp (X Y : EnrichedFunctorCat V A) :
    (λ_ (homObject X Y)).inv ≫ mappingIdentity X ▷ homObject X Y ≫
        mappingComposition X X Y = 𝟙 (homObject X Y) := by
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Y.toEnrichedFunctor
  intro a
  simp only [Category.assoc, Category.id_comp]
  rw [mappingComposition_π]
  have ht := tensorHom_comp_tensorHom (mappingIdentity X) (𝟙 (homObject X Y))
    (homProjection X X a) (homProjection X Y a)
  simp only [tensorHom_id, Category.id_comp, mappingIdentity_π] at ht
  rw [← Category.assoc (mappingIdentity X ▷ homObject X Y), ht, tensorHom_def',
    Category.assoc, ← leftUnitor_inv_naturality_assoc,
    closedLeftIdentity (X.toEnrichedFunctor.obj a)
      (Y.toEnrichedFunctor.obj a), Category.comp_id]

/-- The original identity is a right identity on the entire original mapping object. -/
theorem mappingComposition_id (X Y : EnrichedFunctorCat V A) :
    (ρ_ (homObject X Y)).inv ≫ homObject X Y ◁ mappingIdentity Y ≫
        mappingComposition X Y Y = 𝟙 (homObject X Y) := by
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Y.toEnrichedFunctor
  intro a
  simp only [Category.assoc, Category.id_comp]
  rw [mappingComposition_π]
  have ht := tensorHom_comp_tensorHom (𝟙 (homObject X Y)) (mappingIdentity Y)
    (homProjection X Y a) (homProjection Y Y a)
  simp only [id_tensorHom, Category.id_comp, mappingIdentity_π] at ht
  rw [← Category.assoc (homObject X Y ◁ mappingIdentity Y), ht, tensorHom_def,
    Category.assoc, ← rightUnitor_inv_naturality_assoc,
    closedRightIdentity (X.toEnrichedFunctor.obj a)
      (Y.toEnrichedFunctor.obj a), Category.comp_id]

/-- The full original mapping composition is associative under the actual ambient associator. -/
theorem mappingComposition_assoc (W X Y Z : EnrichedFunctorCat V A) :
    (α_ (homObject W X) (homObject X Y) (homObject Y Z)).inv ≫
        mappingComposition W X Y ▷ homObject Y Z ≫ mappingComposition W Y Z =
      homObject W X ◁ mappingComposition X Y Z ≫ mappingComposition W X Z := by
  apply Enriched.weightedEnd.hom_ext W.toEnrichedFunctor Z.toEnrichedFunctor
  intro a
  simp only [Category.assoc]
  rw [mappingComposition_π, mappingComposition_π,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    mappingComposition_π, mappingComposition_π]
  have hL := tensorHom_comp_tensorHom (homProjection W X a ⊗ₘ homProjection X Y a)
    (homProjection Y Z a)
    (eComp V (W.toEnrichedFunctor.obj a)
      (X.toEnrichedFunctor.obj a) (Y.toEnrichedFunctor.obj a))
    (𝟙 ((ihom (Y.toEnrichedFunctor.obj a)).obj (Z.toEnrichedFunctor.obj a)))
  simp only [tensorHom_id, Category.comp_id] at hL
  have hR := tensorHom_comp_tensorHom (homProjection W X a)
    (homProjection X Y a ⊗ₘ homProjection Y Z a)
    (𝟙 ((ihom (W.toEnrichedFunctor.obj a)).obj (X.toEnrichedFunctor.obj a)))
    (eComp V (X.toEnrichedFunctor.obj a)
      (Y.toEnrichedFunctor.obj a) (Z.toEnrichedFunctor.obj a))
  simp only [id_tensorHom, Category.comp_id] at hR
  rw [← hL, ← hR]
  have hα :
      (α_ (homObject W X) (homObject X Y) (homObject Y Z)).inv ≫
        ((homProjection W X a ⊗ₘ homProjection X Y a) ⊗ₘ homProjection Y Z a) =
      (homProjection W X a ⊗ₘ (homProjection X Y a ⊗ₘ homProjection Y Z a)) ≫
        (α_ ((ihom (W.toEnrichedFunctor.obj a)).obj (X.toEnrichedFunctor.obj a))
          ((ihom (X.toEnrichedFunctor.obj a)).obj (Y.toEnrichedFunctor.obj a))
          ((ihom (Y.toEnrichedFunctor.obj a)).obj (Z.toEnrichedFunctor.obj a))).inv := by
    apply (cancel_mono
      (α_ ((ihom (W.toEnrichedFunctor.obj a)).obj (X.toEnrichedFunctor.obj a))
        ((ihom (X.toEnrichedFunctor.obj a)).obj (Y.toEnrichedFunctor.obj a))
        ((ihom (Y.toEnrichedFunctor.obj a)).obj (Z.toEnrichedFunctor.obj a))).hom).1
    have h := congrArg
      (fun k => (α_ (homObject W X) (homObject X Y) (homObject Y Z)).inv ≫ k)
      (associator_naturality (homProjection W X a) (homProjection X Y a) (homProjection Y Z a))
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h
  simp only [Category.assoc]
  rw [← Category.assoc _ ((homProjection W X a ⊗ₘ homProjection X Y a) ⊗ₘ homProjection Y Z a), hα]
  simpa only [Category.assoc] using congrArg
    (fun k => (homProjection W X a ⊗ₘ (homProjection X Y a ⊗ₘ homProjection Y Z a)) ≫ k)
    (closedAssociativity (W.toEnrichedFunctor.obj a) (X.toEnrichedFunctor.obj a)
      (Y.toEnrichedFunctor.obj a) (Z.toEnrichedFunctor.obj a))


/-- The original weighted ends form the actual full enriched category of diagrams.
This explicit factory is activated locally by its consumers. -/
@[instance_reducible]
def enrichment : EnrichedCategory V (EnrichedFunctorCat V A) where
  Hom := homObject
  id := mappingIdentity
  comp := mappingComposition
  id_comp := mappingIdentity_comp
  comp_id := mappingComposition_id
  assoc := mappingComposition_assoc

end EndEnrichment

variable [HasProducts.{uA} V] [HasEqualizers V]

/-- The actual weighted end of the original weight and the complete original slice. -/
abbrev mappingObject (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) (b : B) : V :=
  WeightedEndVariance.object F (slice Y b)

/-- Each projection has the original complete internal Hom as target. -/
abbrev projection (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) (b : B) (a : A) :
    mappingObject F Y b ⟶
      (ihom (F.toEnrichedFunctor.obj a)).obj (Y.toEnrichedFunctor.obj (a, b)) :=
  WeightedEndVariance.projection F (slice Y b) a


attribute [local instance] EndEnrichment.enrichment

/-- The actual full parameter map is lifted through the original weighted end. -/
def parameterMap (Y : EnrichedFunctorCat V (A × B)) (b b' : B) :
    (b ⟶[V] b') ⟶ EndEnrichment.homObject (slice Y b) (slice Y b') :=
  GradingConvention.endFromPositive (slice Y b).toEnrichedFunctor
    (slice Y b').toEnrichedFunctor (parameterGrade Y b b')

/-- Every parameter projection is the original full product action. -/
theorem parameterMap_π (Y : EnrichedFunctorCat V (A × B)) (b b' : B) (a : A) :
    parameterMap Y b b' ≫ EndEnrichment.homProjection (slice Y b) (slice Y b') a =
      (fixedLeftPair (V := V) (B := B) a).map b b' ≫
        Y.toEnrichedFunctor.map (a, b) (a, b') := by
  exact GradingConvention.endFromPositive_symmetric_π
    (slice Y b).toEnrichedFunctor (slice Y b').toEnrichedFunctor (parameterGrade Y b b') a

/-- The full parameter identity is the actual original end identity. -/
theorem parameterMap_id (Y : EnrichedFunctorCat V (A × B)) (b : B) :
    eId V b ≫ parameterMap Y b b = EndEnrichment.mappingIdentity (slice Y b) := by
  apply Enriched.weightedEnd.hom_ext (slice Y b).toEnrichedFunctor (slice Y b).toEnrichedFunctor
  intro a
  rw [Category.assoc, parameterMap_π, EndEnrichment.mappingIdentity_π]
  change eId V b ≫ (fixedLeftPair (V := V) (B := B) a).map b b ≫
    Y.toEnrichedFunctor.map (a, b) (a, b) = eId V (Y.toEnrichedFunctor.obj (a, b))
  exact ((fixedLeftPair (V := V) (B := B) a).comp V Y.toEnrichedFunctor).map_id b

/-- The entire parameter composition is the original complete end composition. -/
theorem parameterMap_comp (Y : EnrichedFunctorCat V (A × B)) (b b' b'' : B) :
    eComp V b b' b'' ≫ parameterMap Y b b'' =
      (parameterMap Y b b' ⊗ₘ parameterMap Y b' b'') ≫
        EndEnrichment.mappingComposition (slice Y b) (slice Y b') (slice Y b'') := by
  apply Enriched.weightedEnd.hom_ext (slice Y b).toEnrichedFunctor (slice Y b'').toEnrichedFunctor
  intro a
  simp only [Category.assoc]
  rw [parameterMap_π, EndEnrichment.mappingComposition_π,
    tensorHom_comp_tensorHom_assoc, parameterMap_π, parameterMap_π]
  change eComp V b b' b'' ≫ (fixedLeftPair (V := V) (B := B) a).map b b'' ≫
      Y.toEnrichedFunctor.map (a, b) (a, b'') =
    (((fixedLeftPair (V := V) (B := B) a).map b b' ≫
        Y.toEnrichedFunctor.map (a, b) (a, b')) ⊗ₘ
      ((fixedLeftPair (V := V) (B := B) a).map b' b'' ≫
        Y.toEnrichedFunctor.map (a, b') (a, b''))) ≫
      eComp V (Y.toEnrichedFunctor.obj (a, b)) (Y.toEnrichedFunctor.obj (a, b'))
        (Y.toEnrichedFunctor.obj (a, b''))
  exact ((fixedLeftPair (V := V) (B := B) a).comp V Y.toEnrichedFunctor).map_comp b b' b''

/-- The original full parameter maps give the actual enriched family of slices. -/
def parameterFamily (Y : EnrichedFunctorCat V (A × B)) :
    EnrichedFunctor V B (EnrichedFunctorCat V A) where
  obj b := slice Y b
  map b b' := parameterMap Y b b'
  map_id := parameterMap_id Y
  map_comp := parameterMap_comp Y

/-- The actual original weighted-end representable on the full enriched category. -/
def endRepresentable (F : EnrichedFunctorCat V A) :
    EnrichedFunctor V (EnrichedFunctorCat V A) V :=
  EnrichedFunctor.covariantRepresentable V (EnrichedFunctorCat V A) F

/-- Every complete parameter action acts on the actual original weighted end. -/
def rightObject (F : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V (A × B)) :
    EnrichedFunctorCat V B :=
  ⟨(parameterFamily Y).comp V (endRepresentable F)⟩

/-- The parameter object is the original weighted end of the unchanged slice. -/
theorem rightObject_obj (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) (b : B) :
    (rightObject F Y).toEnrichedFunctor.obj b = mappingObject F Y b := rfl


/-- The entire parameter Hom acts by the original full end composition. -/
theorem rightObject_map_uncurry (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) (b b' : B) :
    MonoidalClosed.uncurry ((rightObject F Y).toEnrichedFunctor.map b b') =
      mappingObject F Y b ◁ parameterMap Y b b' ≫
        EndEnrichment.mappingComposition F (slice Y b) (slice Y b') := by
  change MonoidalClosed.uncurry (parameterMap Y b b' ≫
    MonoidalClosed.curry (EndEnrichment.mappingComposition F (slice Y b) (slice Y b'))) = _
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]

set_option backward.isDefEq.respectTransparency false in
/-- Every full parameter action projects to the original product Hom action. -/
theorem rightObject_map_π (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) (b b' : B) (a : A) :
    MonoidalClosed.uncurry ((rightObject F Y).toEnrichedFunctor.map b b') ≫
        projection F Y b' a =
      (projection F Y b a ⊗ₘ
        ((fixedLeftPair (V := V) (B := B) a).map b b' ≫
          Y.toEnrichedFunctor.map (a, b) (a, b'))) ≫
        eComp V (F.toEnrichedFunctor.obj a) (Y.toEnrichedFunctor.obj (a, b))
          (Y.toEnrichedFunctor.obj (a, b')) := by
  rw [rightObject_map_uncurry]
  change (mappingObject F Y b ◁ parameterMap Y b b' ≫
      EndEnrichment.mappingComposition F (slice Y b) (slice Y b')) ≫
      EndEnrichment.homProjection F (slice Y b') a = _
  rw [Category.assoc, EndEnrichment.mappingComposition_π,
    ← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, parameterMap_π]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem parameter_projection_uncurry (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) (b b' : B) (a : A)
    {P : V} (p : P ⟶ mappingObject F Y b) :
    MonoidalClosed.uncurry (((p ▷ (b ⟶[V] b')) ≫
        MonoidalClosed.uncurry ((rightObject F Y).toEnrichedFunctor.map b b')) ≫
        projection F Y b' a) =
      (α_ (F.toEnrichedFunctor.obj a) P (b ⟶[V] b')).inv ≫
        (MonoidalClosed.uncurry (p ≫ projection F Y b a) ▷ (b ⟶[V] b')) ≫
        MonoidalClosed.uncurry (((fixedLeftPair (V := V) a).comp V
          Y.toEnrichedFunctor).map b b') := by
  rw [Category.assoc, rightObject_map_π, ← tensorHom_id,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, MonoidalClosed.uncurry_eComp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Parameter naturality is precisely the complete second-factor naturality after transposition. -/
theorem parameter_naturality_iff (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (Y : EnrichedFunctorCat V (A × B))
    (p : ∀ b, X.toEnrichedFunctor.obj b ⟶ mappingObject F Y b) (b b' : B) :
    (MonoidalClosed.uncurry (X.toEnrichedFunctor.map b b') ≫ p b' =
      (p b ▷ (b ⟶[V] b')) ≫
        MonoidalClosed.uncurry ((rightObject F Y).toEnrichedFunctor.map b b')) ↔
    (∀ a, MonoidalClosed.uncurry (((fixedLeftPair (V := V) a).comp V
          (F.toEnrichedFunctor.externalTensor X.toEnrichedFunctor)).map b b') ≫
        MonoidalClosed.uncurry (p b' ≫ projection F Y b' a) =
      (MonoidalClosed.uncurry (p b ≫ projection F Y b a) ▷ (b ⟶[V] b')) ≫
        MonoidalClosed.uncurry (((fixedLeftPair (V := V) a).comp V
          Y.toEnrichedFunctor).map b b')) := by
  constructor
  · intro h a
    have hh := congrArg (fun z => MonoidalClosed.uncurry (z ≫ projection F Y b' a)) h
    rw [parameter_projection_uncurry, Category.assoc, MonoidalClosed.uncurry_natural_left] at hh
    have ht := congrArg
      (fun z => (α_ (F.toEnrichedFunctor.obj a) (X.toEnrichedFunctor.obj b)
        (b ⟶[V] b')).hom ≫ z) hh
    rw [external_leftSlice_action]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ht
  · intro h
    apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor (slice Y b').toEnrichedFunctor
    intro a
    apply MonoidalClosed.uncurry_injective
    rw [parameter_projection_uncurry, Category.assoc, MonoidalClosed.uncurry_natural_left]
    have hh := h a
    rw [external_leftSlice_action] at hh
    have ht := congrArg
      (fun z => (α_ (F.toEnrichedFunctor.obj a) (X.toEnrichedFunctor.obj b)
        (b ⟶[V] b')).inv ≫ z) hh
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using ht

/-- The original product transformation lifts through the actual end at each parameter. -/
def transposeComponent (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) (b : B) :
    X.toEnrichedFunctor.obj b ⟶ mappingObject F Y b :=
  GradingConvention.endFromPositive F.toEnrichedFunctor (slice Y b).toEnrichedFunctor
    (gradedTensorOfUnit ((Center.ofBraided V).obj (X.toEnrichedFunctor.obj b))
      ((scalarSliceIso F X b).hom ≫ restrictionMap (fixedRightPair (V := V) b) g))

set_option backward.isDefEq.respectTransparency false in
/-- Each forward component projects to the curry of the original entire product component. -/
theorem transposeComponent_π (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) (b : B) (a : A) :
    transposeComponent F X Y g b ≫ projection F Y b a =
      MonoidalClosed.curry (component g (a, b)) := by
  unfold transposeComponent
  rw [GradingConvention.endFromPositive_symmetric_π, gradedTensorOfUnit_app,
    component_comp, scalarSliceIso_hom_component, restrictionMap_component]
  dsimp only [Center.ofBraided, Center.ofBraidedObj]
  simp only [Iso.inv_hom_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The genuine forward transpose has full enriched parameter naturality. -/
def transpose (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) :
    X ⟶ rightObject F Y :=
  GradedNatTrans.unitOfComponents (transposeComponent F X Y g)
    (by
      intro b b'
      rw [tensorHom_id]
      apply (parameter_naturality_iff F X Y (transposeComponent F X Y g) b b').2
      intro a
      rw [transposeComponent_π, transposeComponent_π,
        MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
      have h := (restrictionMap (fixedLeftPair (V := V) a) g).uncurriedNaturality b b'
      change MonoidalClosed.uncurry (((fixedLeftPair (V := V) a).comp V
        (F.toEnrichedFunctor.externalTensor X.toEnrichedFunctor)).map b b') ≫
        component (restrictionMap (fixedLeftPair (V := V) a) g) b' =
        (component (restrictionMap (fixedLeftPair (V := V) a) g) b ⊗ₘ
          𝟙 (b ⟶[V] b')) ≫ MonoidalClosed.uncurry
            (((fixedLeftPair (V := V) a).comp V Y.toEnrichedFunctor).map b b') at h
      rw [restrictionMap_component, restrictionMap_component, tensorHom_id] at h
      exact h)

set_option backward.isDefEq.respectTransparency false in
/-- The forward transpose retains the original curry at every complete end projection. -/
theorem transpose_component_π (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) (b : B) (a : A) :
    component (transpose F X Y g) b ≫ projection F Y b a =
      MonoidalClosed.curry (component g (a, b)) := by
  change (eHomEquiv V).symm ((transpose F X Y g).app b) ≫ _ = _
  rw [transpose, GradedNatTrans.unitOfComponents_component, transposeComponent_π]

/-- The actual end arrow gives the complete inverse transformation on the original slice. -/
def inverseSlice (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (h : X ⟶ rightObject F Y) (b : B) :
    slice ((leftFunctor F).obj X) b ⟶ slice Y b :=
  (scalarSliceIso F X b).inv ≫
    gradedTensorToUnit ((Center.ofBraided V).obj (X.toEnrichedFunctor.obj b))
      (GradingConvention.endToPositive F.toEnrichedFunctor (slice Y b).toEnrichedFunctor
        (component h b))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse slice has the literal uncurry of each actual end projection. -/
theorem inverseSlice_component (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (h : X ⟶ rightObject F Y) (b : B) (a : A) :
    component (inverseSlice F X Y h b) a =
      MonoidalClosed.uncurry (component h b ≫ projection F Y b a) := by
  rw [inverseSlice, component_comp, scalarSliceIso_inv_component, gradedTensorToUnit_component]
  unfold GradedNatTrans.gradeFirstComponent
  dsimp only [Center.ofBraided, Center.ofBraidedObj]
  rw [GradingConvention.endToPositive_app_symmetric]
  simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The genuine inverse transpose retains full naturality on the whole product Hom. -/
def untranspose (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (h : X ⟶ rightObject F Y) :
    (leftFunctor F).obj X ⟶ Y :=
  GradedNatTrans.unitOfComponents
    (fun p => MonoidalClosed.uncurry (component h p.2 ≫ projection F Y p.2 p.1))
    (product_naturality_of_slices _ _ _
      (by
        intro a a' b
        have hh := (inverseSlice F X Y h b).uncurriedNaturality a a'
        change MonoidalClosed.uncurry
          ((slice ((leftFunctor F).obj X) b).toEnrichedFunctor.map a a') ≫
          component (inverseSlice F X Y h b) a' =
          (component (inverseSlice F X Y h b) a ⊗ₘ 𝟙 (a ⟶[V] a')) ≫
            MonoidalClosed.uncurry ((slice Y b).toEnrichedFunctor.map a a') at hh
        rw [inverseSlice_component, inverseSlice_component, tensorHom_id] at hh
        exact hh)
      (by
        intro a b b'
        have hh : MonoidalClosed.uncurry (X.toEnrichedFunctor.map b b') ≫ component h b' =
            (component h b ▷ (b ⟶[V] b')) ≫
              MonoidalClosed.uncurry ((rightObject F Y).toEnrichedFunctor.map b b') := by
          simpa only [tensorHom_id, component] using h.uncurriedNaturality b b'
        exact (parameter_naturality_iff F X Y (fun b => component h b) b b').1 hh a))

/-- Each inverse product component is the literal uncurry of the original end projection. -/
theorem untranspose_component (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (h : X ⟶ rightObject F Y) (a : A) (b : B) :
    component (untranspose F X Y h) (a, b) =
      MonoidalClosed.uncurry (component h b ≫ projection F Y b a) :=
  GradedNatTrans.unitOfComponents_component _ _ (a, b)

set_option backward.isDefEq.respectTransparency false in
/-- Transposing and untransposing preserves the entire original product transformation. -/
theorem untranspose_transpose (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) :
    untranspose F X Y (transpose F X Y g) = g := by
  apply hom_ext
  rintro ⟨a, b⟩
  rw [untranspose_component, transpose_component_π, MonoidalClosed.uncurry_curry]

set_option backward.isDefEq.respectTransparency false in
/-- Untransposing and transposing preserves the entire original end-valued transformation. -/
theorem transpose_untranspose (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (h : X ⟶ rightObject F Y) :
    transpose F X Y (untranspose F X Y h) = h := by
  apply hom_ext
  intro b
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor (slice Y b).toEnrichedFunctor
  intro a
  rw [transpose_component_π, untranspose_component, MonoidalClosed.curry_uncurry]

/-- The whole genuine external tensor/end Hom correspondence uses the actual original maps. -/
def homEquiv (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) :
    ((leftFunctor F).obj X ⟶ Y) ≃ (X ⟶ rightObject F Y) where
  toFun := transpose F X Y
  invFun := untranspose F X Y
  left_inv := untranspose_transpose F X Y
  right_inv := transpose_untranspose F X Y

/-- The actual evaluation transformation is the inverse transpose of the entire identity. -/
def counitMap (F : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V (A × B)) :
    (leftFunctor F).obj (rightObject F Y) ⟶ Y :=
  untranspose F (rightObject F Y) Y (𝟙 (rightObject F Y))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation uses the literal closed evaluation of each original full end projection. -/
theorem counitMap_component (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) (a : A) (b : B) :
    component (counitMap F Y) (a, b) = MonoidalClosed.uncurry (projection F Y b a) := by
  rw [counitMap, untranspose_component, component_id, Category.id_comp]

/-- Every target transformation gives the actual full end-valued transformation. -/
def rightMap (F : EnrichedFunctorCat V A) {Y Z : EnrichedFunctorCat V (A × B)} (q : Y ⟶ Z) :
    rightObject F Y ⟶ rightObject F Z :=
  transpose F (rightObject F Y) Z (counitMap F Y ≫ q)

set_option backward.isDefEq.respectTransparency false in
/-- The target map projects to literal postcomposition in the original internal Hom. -/
theorem rightMap_component_π (F : EnrichedFunctorCat V A)
    {Y Z : EnrichedFunctorCat V (A × B)} (q : Y ⟶ Z) (b : B) (a : A) :
    component (rightMap F q) b ≫ projection F Z b a =
      projection F Y b a ≫ (ihom (F.toEnrichedFunctor.obj a)).map (component q (a, b)) := by
  rw [rightMap, transpose_component_π, component_comp, counitMap_component,
    MonoidalClosed.curry_natural_right, MonoidalClosed.curry_uncurry]

set_option backward.isDefEq.respectTransparency false in
/-- The complete target component is the original weighted-end diagram map
on the unchanged slice. -/
theorem rightMap_component (F : EnrichedFunctorCat V A)
    {Y Z : EnrichedFunctorCat V (A × B)} (q : Y ⟶ Z) (b : B) :
    component (rightMap F q) b =
      WeightedEndVariance.post F (restrictionMap (fixedRightPair (V := V) b) q) := by
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor (slice Z b).toEnrichedFunctor
  intro a
  have hp := WeightedEndVariance.post_projection F
    (restrictionMap (fixedRightPair (V := V) b) q) a
  rw [restrictionMap_component] at hp
  exact (rightMap_component_π F q b a).trans hp.symm

set_option backward.isDefEq.respectTransparency false in
/-- The original parameterized weighted ends act functorially on all target transformations. -/
def rightFunctor (F : EnrichedFunctorCat V A) :
    EnrichedFunctorCat V (A × B) ⥤ EnrichedFunctorCat V B where
  obj := rightObject F
  map := rightMap F
  map_id Y := by
    apply hom_ext
    intro b
    rw [rightMap_component, component_id]
    have hr : restrictionMap (fixedRightPair (V := V) b) (𝟙 Y) = 𝟙 (slice Y b) :=
      (restriction (fixedRightPair (V := V) b)).map_id Y
    rw [hr]
    exact WeightedEndVariance.post_id F (slice Y b)
  map_comp q r := by
    apply hom_ext
    intro b
    rw [rightMap_component, component_comp, rightMap_component, rightMap_component]
    have hr : restrictionMap (fixedRightPair (V := V) b) (q ≫ r) =
        restrictionMap (fixedRightPair (V := V) b) q ≫
          restrictionMap (fixedRightPair (V := V) b) r :=
      (restriction (fixedRightPair (V := V) b)).map_comp q r
    rw [hr]
    exact WeightedEndVariance.post_comp F _ _

set_option backward.isDefEq.respectTransparency false in
/-- The full inverse transpose is natural in every original second-factor transformation. -/
theorem untranspose_naturality_left (F : EnrichedFunctorCat V A)
    {X X' : EnrichedFunctorCat V B} (f : X' ⟶ X)
    (Y : EnrichedFunctorCat V (A × B)) (h : X ⟶ rightObject F Y) :
    untranspose F X' Y (f ≫ h) = (leftFunctor F).map f ≫ untranspose F X Y h := by
  apply hom_ext
  rintro ⟨a, b⟩
  rw [untranspose_component, component_comp, Category.assoc,
    MonoidalClosed.uncurry_natural_left, component_comp, leftFunctor_map_component,
    untranspose_component, id_tensorHom]

set_option backward.isDefEq.respectTransparency false in
/-- The full forward transpose is natural in every original second-factor transformation. -/
theorem transpose_naturality_left (F : EnrichedFunctorCat V A)
    {X X' : EnrichedFunctorCat V B} (f : X' ⟶ X)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) :
    transpose F X' Y ((leftFunctor F).map f ≫ g) = f ≫ transpose F X Y g := by
  apply hom_ext
  intro b
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor (slice Y b).toEnrichedFunctor
  intro a
  rw [transpose_component_π, component_comp, leftFunctor_map_component,
    id_tensorHom, MonoidalClosed.curry_natural_left, component_comp,
    Category.assoc, transpose_component_π]

set_option backward.isDefEq.respectTransparency false in
/-- The full forward transpose is natural in the entire original target transformation. -/
theorem transpose_naturality_right (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    {Y Z : EnrichedFunctorCat V (A × B)} (g : (leftFunctor F).obj X ⟶ Y) (q : Y ⟶ Z) :
    transpose F X Z (g ≫ q) = transpose F X Y g ≫ (rightFunctor F).map q := by
  apply hom_ext
  intro b
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor (slice Z b).toEnrichedFunctor
  intro a
  rw [transpose_component_π, component_comp, component_comp, Category.assoc]
  change MonoidalClosed.curry (component g (a, b) ≫ component q (a, b)) =
    component (transpose F X Y g) b ≫ component (rightMap F q) b ≫ projection F Z b a
  rw [rightMap_component_π, ← Category.assoc, transpose_component_π,
    MonoidalClosed.curry_natural_right]

/-- The full ordinary adjunction is derived from the actual weighted-end
universal correspondence. -/
def adjunction (F : EnrichedFunctorCat V A) : leftFunctor (B := B) F ⊣ rightFunctor F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv F
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        exact untranspose_naturality_left F f Y g
      homEquiv_naturality_right := by
        intro X Y Y' f g
        exact transpose_naturality_right F X f g }

omit [HasProducts.{uA} V] [HasEqualizers V] in
/-- Every original weight transformation acts on the entire external tensor. -/
def leftWeightMap {F F' : EnrichedFunctorCat V A} (p : F ⟶ F')
    (X : EnrichedFunctorCat V B) : (leftFunctor F).obj X ⟶ (leftFunctor F').obj X :=
  EnrichedFunctor.externalMap p (𝟙 X)

set_option backward.isDefEq.respectTransparency false in
omit [HasProducts.{uA} V] [HasEqualizers V] in
/-- The weight action tensors the original complete weight component. -/
theorem leftWeightMap_component {F F' : EnrichedFunctorCat V A} (p : F ⟶ F')
    (X : EnrichedFunctorCat V B) (a : A) (b : B) :
    component (leftWeightMap p X) (a, b) =
      component p a ⊗ₘ 𝟙 (X.toEnrichedFunctor.obj b) := by
  change (eHomEquiv V).symm ((EnrichedFunctor.externalMap p (𝟙 X)).app (a, b)) = _
  rw [EnrichedFunctor.externalMap_component]
  exact congrArg (fun q => component p a ⊗ₘ q) (component_id X b)

set_option backward.isDefEq.respectTransparency false in
omit [HasProducts.{uA} V] [HasEqualizers V] in
/-- Both complete external input actions commute. -/
theorem leftWeightMap_naturality {F F' : EnrichedFunctorCat V A} (p : F ⟶ F')
    {X X' : EnrichedFunctorCat V B} (f : X ⟶ X') :
    (leftFunctor F).map f ≫ leftWeightMap p X' =
      leftWeightMap p X ≫ (leftFunctor F').map f := by
  apply hom_ext
  rintro ⟨a, b⟩
  rw [component_comp, component_comp, leftFunctor_map_component,
    leftFunctor_map_component, leftWeightMap_component, leftWeightMap_component,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, Category.comp_id, Category.id_comp]

/-- The original weight map gives the full contravariant transformation of parameterized ends. -/
def sourceMap {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F)
    (Y : EnrichedFunctorCat V (A × B)) : rightObject F Y ⟶ rightObject F' Y :=
  transpose F' (rightObject F Y) Y (leftWeightMap p (rightObject F Y) ≫ counitMap F Y)

set_option backward.isDefEq.respectTransparency false in
/-- Source variance projects to the original entire internal-Hom precomposition. -/
theorem sourceMap_component_π {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F)
    (Y : EnrichedFunctorCat V (A × B)) (b : B) (a : A) :
    component (sourceMap p Y) b ≫ projection F' Y b a =
      projection F Y b a ≫ (MonoidalClosed.pre (component p a)).app
        (Y.toEnrichedFunctor.obj (a, b)) := by
  rw [sourceMap, transpose_component_π, component_comp, leftWeightMap_component,
    counitMap_component, tensorHom_id, ← MonoidalClosed.curry_pre_app,
    MonoidalClosed.curry_uncurry]

set_option backward.isDefEq.respectTransparency false in
/-- The complete source component is the original weighted-end weight map. -/
theorem sourceMap_component {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F)
    (Y : EnrichedFunctorCat V (A × B)) (b : B) :
    component (sourceMap p Y) b = WeightedEndVariance.pre p (slice Y b) := by
  apply Enriched.weightedEnd.hom_ext F'.toEnrichedFunctor (slice Y b).toEnrichedFunctor
  intro a
  exact (sourceMap_component_π p Y b a).trans
    (WeightedEndVariance.pre_projection p (slice Y b) a).symm

set_option backward.isDefEq.respectTransparency false in
/-- Source variance retains the original identity on every complete parameterized end. -/
theorem sourceMap_id (F : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V (A × B)) :
    sourceMap (𝟙 F) Y = 𝟙 (rightObject F Y) := by
  apply hom_ext
  intro b
  rw [sourceMap_component, component_id]
  exact WeightedEndVariance.pre_id F (slice Y b)

set_option backward.isDefEq.respectTransparency false in
/-- Source composition retains the original contravariant order and all original weight maps. -/
theorem sourceMap_comp {F F' F'' : EnrichedFunctorCat V A} (p : F' ⟶ F) (q : F'' ⟶ F')
    (Y : EnrichedFunctorCat V (A × B)) :
    sourceMap (q ≫ p) Y = sourceMap p Y ≫ sourceMap q Y := by
  apply hom_ext
  intro b
  rw [sourceMap_component, component_comp, sourceMap_component, sourceMap_component]
  exact WeightedEndVariance.pre_comp q p (slice Y b)

set_option backward.isDefEq.respectTransparency false in
/-- The entire original source and target actions commute on parameterized weighted ends. -/
theorem sourceMap_naturality {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F)
    {Y Z : EnrichedFunctorCat V (A × B)} (q : Y ⟶ Z) :
    (rightFunctor F).map q ≫ sourceMap p Z =
      sourceMap p Y ≫ (rightFunctor F').map q := by
  apply hom_ext
  intro b
  change component (rightMap F q ≫ sourceMap p Z) b =
    component (sourceMap p Y ≫ rightMap F' q) b
  rw [component_comp, component_comp, rightMap_component, rightMap_component,
    sourceMap_component, sourceMap_component]
  exact WeightedEndVariance.pre_post p (restrictionMap (fixedRightPair (V := V) b) q)

set_option backward.isDefEq.respectTransparency false in
/-- The full transpose is contravariantly natural in every original weight transformation. -/
theorem transpose_naturality_source {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F)
    (X : EnrichedFunctorCat V B) (Y : EnrichedFunctorCat V (A × B))
    (g : (leftFunctor F).obj X ⟶ Y) :
    transpose F' X Y (leftWeightMap p X ≫ g) = transpose F X Y g ≫ sourceMap p Y := by
  apply hom_ext
  intro b
  apply Enriched.weightedEnd.hom_ext F'.toEnrichedFunctor (slice Y b).toEnrichedFunctor
  intro a
  rw [transpose_component_π, component_comp, leftWeightMap_component,
    tensorHom_id, ← MonoidalClosed.curry_pre_app, component_comp, Category.assoc,
    sourceMap_component_π, ← Category.assoc, transpose_component_π]

/-- The actual contravariant weight maps form a natural family of the actual right adjoints. -/
def sourceNatTrans {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F) :
    rightFunctor (B := B) F ⟶ rightFunctor F' where
  app := sourceMap p
  naturality _ _ q := sourceMap_naturality p q

/-- The unit is the forward transpose of the entire original external identity. -/
theorem adjunction_unit_app (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B) :
    (adjunction F).unit.app X =
      transpose F X ((leftFunctor F).obj X) (𝟙 ((leftFunctor F).obj X)) := rfl

/-- The counit is the actual evaluation map constructed from the original weighted end. -/
theorem adjunction_counit_app (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) : (adjunction F).counit.app Y = counitMap F Y := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Each unit projection is the curry of the original entire identity tensor component. -/
theorem adjunction_unit_component_π (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (b : B) (a : A) :
    component ((adjunction F).unit.app X) b ≫ projection F ((leftFunctor F).obj X) b a =
      MonoidalClosed.curry (𝟙 (F.toEnrichedFunctor.obj a ⊗ X.toEnrichedFunctor.obj b)) := by
  have h := transpose_component_π F X ((leftFunctor F).obj X)
    (𝟙 ((leftFunctor F).obj X)) b a
  rw [component_id] at h
  exact h

/-- The actual left triangle retains the complete original external object and both maps. -/
theorem adjunction_left_triangle (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B) :
    (leftFunctor F).map ((adjunction F).unit.app X) ≫
      (adjunction F).counit.app ((leftFunctor F).obj X) = 𝟙 ((leftFunctor F).obj X) :=
  (adjunction F).left_triangle_components X

/-- The actual right triangle retains the entire original parameterized weighted end. -/
theorem adjunction_right_triangle (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) :
    (adjunction F).unit.app ((rightFunctor F).obj Y) ≫
      (rightFunctor F).map ((adjunction F).counit.app Y) = 𝟙 ((rightFunctor F).obj Y) :=
  (adjunction F).right_triangle_components Y

set_option backward.isDefEq.respectTransparency false in
/-- The left triangle uses the complete original unit and evaluation components. -/
theorem adjunction_left_triangle_component (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (a : A) (b : B) :
    (𝟙 (F.toEnrichedFunctor.obj a) ⊗ₘ component ((adjunction F).unit.app X) b) ≫
      MonoidalClosed.uncurry (projection F ((leftFunctor F).obj X) b a) =
        𝟙 (F.toEnrichedFunctor.obj a ⊗ X.toEnrichedFunctor.obj b) := by
  have h := congrArg (fun q => component q (a, b)) (adjunction_left_triangle F X)
  change component ((leftFunctor F).map ((adjunction F).unit.app X) ≫
    counitMap F ((leftFunctor F).obj X)) (a, b) =
      component (𝟙 ((leftFunctor F).obj X)) (a, b) at h
  rw [component_comp, leftFunctor_map_component] at h
  let i : X.toEnrichedFunctor.obj b ⟶ mappingObject F ((leftFunctor F).obj X) b :=
    component ((adjunction F).unit.app X) b
  let q : F.toEnrichedFunctor.obj a ⊗ mappingObject F ((leftFunctor F).obj X) b ⟶
      F.toEnrichedFunctor.obj a ⊗ X.toEnrichedFunctor.obj b :=
    component (counitMap F ((leftFunctor F).obj X)) (a, b)
  have hq : q = MonoidalClosed.uncurry (projection F ((leftFunctor F).obj X) b a) :=
    counitMap_component F ((leftFunctor F).obj X) a b
  have hh : (𝟙 (F.toEnrichedFunctor.obj a) ⊗ₘ i) ≫ q =
      𝟙 (F.toEnrichedFunctor.obj a ⊗ X.toEnrichedFunctor.obj b) :=
    h.trans (component_id ((leftFunctor F).obj X) (a, b))
  rw [hq] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- The right triangle keeps the complete original weighted-end diagram map at each parameter. -/
theorem adjunction_right_triangle_component (F : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V (A × B)) (b : B) :
    component ((adjunction F).unit.app (rightObject F Y)) b ≫
      WeightedEndVariance.post F (restrictionMap (fixedRightPair (V := V) b) (counitMap F Y)) =
        𝟙 (mappingObject F Y b) := by
  have h := congrArg (fun q => component q b) (adjunction_right_triangle F Y)
  change component ((adjunction F).unit.app (rightObject F Y) ≫
    rightMap F ((adjunction F).counit.app Y)) b = component (𝟙 (rightObject F Y)) b at h
  rw [component_comp, rightMap_component, adjunction_counit_app, component_id] at h
  exact h

section TensorSlice

variable {I : Type uA} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]

set_option backward.isDefEq.respectTransparency false in
omit [HasProducts.{uA} V] [HasEqualizers V] in
/-- Restricting the original tensor diagram gives its original fixed-right-tensor slice. -/
theorem slice_restriction_fixedRightTensor (d : EnrichedMonoidalCategoryData V I)
    (G : EnrichedFunctorCat V I) (b : I) :
    slice ((restriction d.tensorEnrichedFunctor).obj G) b =
      restrictionObject (Enriched.SphereOperator.fixedRightTensor d b) G := by
  apply congrArg EnrichedFunctorCat.mk
  refine EnrichedFunctor.ext V
    (F := (fixedRightPair (V := V) b).comp V
      ((restriction d.tensorEnrichedFunctor).obj G).toEnrichedFunctor)
    (G := (Enriched.SphereOperator.fixedRightTensor d b).comp V G.toEnrichedFunctor)
    (fun a => rfl) ?_
  intro a a'
  change (((ρ_ (a ⟶[V] a')).inv ≫ (𝟙 (a ⟶[V] a') ⊗ₘ eId V b)) ≫
      (d.tensorMap a a' b b ≫ G.toEnrichedFunctor.map (a ⊗ b) (a' ⊗ b))) ≫ 𝟙 _ =
    (((ρ_ (a ⟶[V] a')).inv ≫ (𝟙 (a ⟶[V] a') ⊗ₘ eId V b)) ≫
      d.tensorMap a a' b b) ≫ G.toEnrichedFunctor.map (a ⊗ b) (a' ⊗ b)
  rw [Category.comp_id]
  exact (Category.assoc _ _ _).symm

/-- The native tensor specialization is the actual end over the original fixed-right tensor. -/
theorem mappingObject_restriction_fixedRightTensor (d : EnrichedMonoidalCategoryData V I)
    (F G : EnrichedFunctorCat V I) (b : I) :
    mappingObject F ((restriction d.tensorEnrichedFunctor).obj G) b =
      Enriched.weightedEnd F.toEnrichedFunctor
        ((Enriched.SphereOperator.fixedRightTensor d b).comp V G.toEnrichedFunctor) := by
  exact congrArg (fun Z => WeightedEndVariance.object F Z)
    (slice_restriction_fixedRightTensor d G b)

end TensorSlice

section Coefficients

set_option backward.isDefEq.respectTransparency false in
omit [HasProducts.{uA} V] [HasEqualizers V] in
private theorem external_braiding_natural (F : EnrichedFunctor V A V)
    (X : EnrichedFunctor V B V) (p p' : A × B) :
    MonoidalClosed.uncurry ((F.externalTensor X).map p p') ≫
        (β_ (F.obj p'.1) (X.obj p'.2)).hom =
      ((β_ (F.obj p.1) (X.obj p.2)).hom ⊗ₘ
        (β_ (p.1 ⟶[V] p'.1) (p.2 ⟶[V] p'.2)).hom) ≫
        MonoidalClosed.uncurry ((X.externalTensor F).map (p.2, p.1) (p'.2, p'.1)) := by
  rw [EnrichedFunctor.externalTensor_uncurry, EnrichedFunctor.externalTensor_uncurry,
    Category.assoc, braiding_naturality]
  rw [← Category.assoc, EnrichedDayKernel.BraidingCoherence.tensorMu_swap, Category.assoc]

omit [SymmetricCategory V] [MonoidalClosed V] [HasProducts.{uA} V] [HasEqualizers V] in
private theorem scalar_action_natural (M : V) {U U' K K' P Q : V}
    (f : U ⊗ P ⟶ U') (g : K ⊗ Q ⟶ K') (q : U ⟶ K) (q' : U' ⟶ K') (r : P ⟶ Q)
    (h : f ≫ q' = (q ⊗ₘ r) ≫ g) :
    (α_ M U P).hom ≫ M ◁ f ≫ M ◁ q' =
      ((M ◁ q) ⊗ₘ r) ≫ (α_ M K Q).hom ≫ M ◁ g := by
  rw [← whiskerLeft_comp, h, whiskerLeft_comp]
  have ha := associator_naturality (𝟙 M) q r
  simpa only [id_tensorHom, Category.assoc] using
    congrArg (fun z => z ≫ M ◁ g) ha.symm

set_option backward.isDefEq.respectTransparency false in
omit [HasProducts.{uA} V] [HasEqualizers V] in
private theorem scalar_external_braiding_natural (M : V)
    (F : EnrichedFunctor V A V) (X : EnrichedFunctor V B V) (p p' : A × B) :
    MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M (F.externalTensor X)).map p p') ≫
        M ◁ (β_ (F.obj p'.1) (X.obj p'.2)).hom =
      ((M ◁ (β_ (F.obj p.1) (X.obj p.2)).hom) ⊗ₘ
        (β_ (p.1 ⟶[V] p'.1) (p.2 ⟶[V] p'.2)).hom) ≫
        MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M (X.externalTensor F)).map
          (p.2, p.1) (p'.2, p'.1)) := by
  rw [EnrichedFunctor.tensorLeft_map_uncurry, EnrichedFunctor.tensorLeft_map_uncurry]
  rw [Category.assoc]
  exact scalar_action_natural M _ _ _ _ _ (external_braiding_natural F X p p')

omit [HasProducts.{uA} V] [HasEqualizers V] [MonoidalClosed V] in
/-- The coefficient interchange is the original full value braiding and associators. -/
def scalarExternalComponentIso (M U K : V) : U ⊗ (M ⊗ K) ≅ M ⊗ (U ⊗ K) :=
  (β_ U (M ⊗ K)) ≪≫ (α_ M K U) ≪≫ whiskerLeftIso M (β_ K U)

omit [HasProducts.{uA} V] [HasEqualizers V] [MonoidalClosed V] in
/-- The complete scalar interchange is the canonical crossing of the coefficient and weight. -/
theorem scalarExternalComponentIso_hom (M U K : V) :
    (scalarExternalComponentIso M U K).hom =
      (α_ U M K).inv ≫ ((β_ U M).hom ▷ K) ≫ (α_ M U K).hom := by
  simp only [scalarExternalComponentIso, Iso.trans_hom, whiskerLeftIso_hom]
  rw [braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp, SymmetricCategory.symmetry]
  simp only [whiskerLeft_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
omit [HasProducts.{uA} V] [HasEqualizers V] in
/-- The canonical coefficient interchange respects the entire two-factor enriched Hom action. -/
theorem scalarExternal_full_naturality (M : V) (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (p p' : A × B) :
    MonoidalClosed.uncurry
        (((leftFunctor F).obj (tensorLeftObject M X)).toEnrichedFunctor.map p p') ≫
        (scalarExternalComponentIso M (F.toEnrichedFunctor.obj p'.1)
          (X.toEnrichedFunctor.obj p'.2)).hom =
      ((scalarExternalComponentIso M (F.toEnrichedFunctor.obj p.1)
          (X.toEnrichedFunctor.obj p.2)).hom ⊗ₘ 𝟙 (p ⟶[V] p')) ≫
        MonoidalClosed.uncurry
          ((tensorLeftObject M ((leftFunctor F).obj X)).toEnrichedFunctor.map p p') := by
  have h1 := external_braiding_natural F.toEnrichedFunctor
    (EnrichedFunctor.tensorLeft M X.toEnrichedFunctor) p p'
  have h2 := externalTensorScalar_full_naturality M X.toEnrichedFunctor F.toEnrichedFunctor
    (p.2, p.1) (p'.2, p'.1)
  have h3 := scalar_external_braiding_natural M X.toEnrichedFunctor F.toEnrichedFunctor
    (p.2, p.1) (p'.2, p'.1)
  simp only [tensorHom_id] at h2
  let U := F.toEnrichedFunctor.obj p.1
  let U' := F.toEnrichedFunctor.obj p'.1
  let K := X.toEnrichedFunctor.obj p.2
  let K' := X.toEnrichedFunctor.obj p'.2
  let P : V := p.1 ⟶[V] p'.1
  let Q : V := p.2 ⟶[V] p'.2
  let f : (U ⊗ (M ⊗ K)) ⊗ (P ⊗ Q) ⟶ U' ⊗ (M ⊗ K') :=
    MonoidalClosed.uncurry ((F.toEnrichedFunctor.externalTensor
      (EnrichedFunctor.tensorLeft M X.toEnrichedFunctor)).map p p')
  let g : ((M ⊗ K) ⊗ U) ⊗ (Q ⊗ P) ⟶ (M ⊗ K') ⊗ U' :=
    MonoidalClosed.uncurry (((EnrichedFunctor.tensorLeft M X.toEnrichedFunctor).externalTensor
      F.toEnrichedFunctor).map (p.2, p.1) (p'.2, p'.1))
  let h : (M ⊗ (K ⊗ U)) ⊗ (Q ⊗ P) ⟶ M ⊗ (K' ⊗ U') :=
    MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M
      (X.toEnrichedFunctor.externalTensor F.toEnrichedFunctor)).map (p.2, p.1) (p'.2, p'.1))
  let k : (M ⊗ (U ⊗ K)) ⊗ (P ⊗ Q) ⟶ M ⊗ (U' ⊗ K') :=
    MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M
      (F.toEnrichedFunctor.externalTensor X.toEnrichedFunctor)).map p p')
  have h1' : f ≫ (β_ U' (M ⊗ K')).hom =
      ((β_ U (M ⊗ K)).hom ⊗ₘ (β_ P Q).hom) ≫ g := h1
  have h2' : g ≫ (α_ M K' U').hom = ((α_ M K U).hom ▷ (Q ⊗ P)) ≫ h := h2
  have h3' : h ≫ M ◁ (β_ K' U').hom =
      ((M ◁ (β_ K U).hom) ⊗ₘ (β_ Q P).hom) ≫ k := h3
  change f ≫ (scalarExternalComponentIso M U' K').hom =
    ((scalarExternalComponentIso M U K).hom ⊗ₘ 𝟙 (P ⊗ Q)) ≫ k
  simp only [scalarExternalComponentIso, Iso.trans_hom, whiskerLeftIso_hom]
  rw [reassoc_of% h1', reassoc_of% h2', h3', ← tensorHom_id,
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id, Category.assoc, SymmetricCategory.symmetry]

omit [HasProducts.{uA} V] [HasEqualizers V] in
/-- The actual external scalar comparison retains both entire component maps. -/
def scalarExternalIso (M : V) (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B) :
    (leftFunctor F).obj (tensorLeftObject M X) ≅ tensorLeftObject M ((leftFunctor F).obj X) :=
  isoOfComponents _ _
    (fun p => scalarExternalComponentIso M (F.toEnrichedFunctor.obj p.1)
      (X.toEnrichedFunctor.obj p.2)) (scalarExternal_full_naturality M F X)

omit [HasProducts.{uA} V] [HasEqualizers V] in
/-- The forward scalar comparison retains its full canonical coefficient crossing. -/
theorem scalarExternalIso_hom_component (M : V) (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (a : A) (b : B) :
    component (scalarExternalIso M F X).hom (a, b) =
      (scalarExternalComponentIso M (F.toEnrichedFunctor.obj a) (X.toEnrichedFunctor.obj b)).hom :=
  isoOfComponents_hom_component _ _ _ _ (a, b)

omit [HasProducts.{uA} V] [HasEqualizers V] in
/-- The inverse scalar comparison retains the actual inverse coefficient crossing. -/
theorem scalarExternalIso_inv_component (M : V) (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (a : A) (b : B) :
    component (scalarExternalIso M F X).inv (a, b) =
      (scalarExternalComponentIso M (F.toEnrichedFunctor.obj a) (X.toEnrichedFunctor.obj b)).inv :=
  isoOfComponents_inv_component _ _ _ _ (a, b)

/-- The original scalar comparison gives the actual correspondence of its full source maps. -/
def scalarExternalHomEquiv (M : V) (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) :
    (tensorLeftObject M ((leftFunctor F).obj X) ⟶ Y) ≃
      ((leftFunctor F).obj (tensorLeftObject M X) ⟶ Y) where
  toFun f := (scalarExternalIso M F X).hom ≫ f
  invFun g := (scalarExternalIso M F X).inv ≫ g
  left_inv f := by simp only [Iso.inv_hom_id_assoc]
  right_inv g := by simp only [Iso.hom_inv_id_assoc]

/-- The whole transpose retains every ambient coefficient in its genuine canonical center grade. -/
def gradedHomEquiv (M : V) (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) :
    GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor ≃
    GradedNatTrans ((Center.ofBraided V).obj M) X.toEnrichedFunctor
      (rightObject F Y).toEnrichedFunctor :=
  (gradedTensorHomEquiv ((Center.ofBraided V).obj M) ((leftFunctor F).obj X) Y).trans
    ((scalarExternalHomEquiv M F X Y).trans
      ((homEquiv F (tensorLeftObject M X) Y).trans
        (gradedTensorHomEquiv ((Center.ofBraided V).obj M) X (rightObject F Y)).symm))

set_option backward.isDefEq.respectTransparency false in
/-- Every coefficient projects to the curry of the original full graded product component. -/
theorem gradedHomEquiv_apply_π (M : V) (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (Y : EnrichedFunctorCat V (A × B))
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) (b : B) (a : A) :
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
        (gradedHomEquiv M F X Y t) b ≫ projection F Y b a =
      MonoidalClosed.curry
        ((scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
          (X.toEnrichedFunctor.obj b)).hom ≫
            GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (a, b)) := by
  change GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
    (gradedTensorOfUnit ((Center.ofBraided V).obj M)
      (transpose F (tensorLeftObject M X) Y
        ((scalarExternalIso M F X).hom ≫
          gradedTensorToUnit ((Center.ofBraided V).obj M) t))) b ≫ _ = _
  rw [gradedTensorOfUnit_gradeFirstComponent]
  let f : tensorLeftObject M ((leftFunctor F).obj X) ⟶ Y :=
    gradedTensorToUnit ((Center.ofBraided V).obj M) t
  have hp := transpose_component_π F (tensorLeftObject M X) Y
    ((scalarExternalIso M F X).hom ≫ f) b a
  rw [component_comp, scalarExternalIso_hom_component] at hp
  exact hp.trans (congrArg
    (fun z => MonoidalClosed.curry
      ((scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
        (X.toEnrichedFunctor.obj b)).hom ≫ z))
    (gradedTensorToUnit_component ((Center.ofBraided V).obj M) t (a, b)))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse keeps the entire coefficient, end projection and actual inverse scalar crossing. -/
theorem gradedHomEquiv_symm_gradeFirst (M : V) (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (Y : EnrichedFunctorCat V (A × B))
    (h : GradedNatTrans ((Center.ofBraided V).obj M) X.toEnrichedFunctor
      (rightObject F Y).toEnrichedFunctor) (a : A) (b : B) :
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
        ((gradedHomEquiv M F X Y).symm h) (a, b) =
      (scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
        (X.toEnrichedFunctor.obj b)).inv ≫
          MonoidalClosed.uncurry
            (GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) h b ≫
              projection F Y b a) := by
  change GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
    (gradedTensorOfUnit ((Center.ofBraided V).obj M)
      ((scalarExternalIso M F X).inv ≫
        untranspose F (tensorLeftObject M X) Y
          (gradedTensorToUnit ((Center.ofBraided V).obj M) h))) (a, b) = _
  rw [gradedTensorOfUnit_gradeFirstComponent, component_comp, scalarExternalIso_inv_component,
    untranspose_component, gradedTensorToUnit_component]

omit [HasProducts.{uA} V] [HasEqualizers V] [MonoidalClosed V] in
/-- The entire coefficient interchange is natural in all three original value maps. -/
theorem scalarExternalComponentIso_naturality {M M' U U' K K' : V}
    (r : M ⟶ M') (f : U ⟶ U') (g : K ⟶ K') :
    (f ⊗ₘ (r ⊗ₘ g)) ≫ (scalarExternalComponentIso M' U' K').hom =
      (scalarExternalComponentIso M U K).hom ≫ (r ⊗ₘ (f ⊗ₘ g)) := by
  simp only [scalarExternalComponentIso, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
  rw [braiding_naturality_assoc, associator_naturality_assoc]
  have h : (r ⊗ₘ (g ⊗ₘ f)) ≫ M' ◁ (β_ K' U').hom =
      M ◁ (β_ K U).hom ≫ (r ⊗ₘ (f ⊗ₘ g)) := by
    rw [← id_tensorHom, ← id_tensorHom,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, braiding_naturality]
  simpa only [Category.assoc] using congrArg
    (fun z => (β_ U (M ⊗ K)).hom ≫ (α_ M K U).hom ≫ z) h

set_option backward.isDefEq.respectTransparency false in
/-- The full transpose is natural in every actual ambient coefficient arrow. -/
theorem gradedHomEquiv_regrade {M M' : V} (r : M' ⟶ M)
    (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B))
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv M' F X Y (GradedNatTrans.regrade ((Center.ofBraided V).map r) t) =
      GradedNatTrans.regrade ((Center.ofBraided V).map r) (gradedHomEquiv M F X Y t) := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj M')
  intro b
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor (slice Y b).toEnrichedFunctor
  intro a
  rw [gradedHomEquiv_apply_π, GradedNatTrans.gradeFirstComponent_regrade,
    GradedNatTrans.gradeFirstComponent_regrade, Category.assoc,
    gradedHomEquiv_apply_π, ← MonoidalClosed.curry_natural_left]
  change MonoidalClosed.curry
      ((scalarExternalComponentIso M' (F.toEnrichedFunctor.obj a)
        (X.toEnrichedFunctor.obj b)).hom ≫ (r ▷
          (F.toEnrichedFunctor.obj a ⊗ X.toEnrichedFunctor.obj b)) ≫
          GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (a, b)) =
    MonoidalClosed.curry
      (F.toEnrichedFunctor.obj a ◁ (r ▷ X.toEnrichedFunctor.obj b) ≫
        (scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
          (X.toEnrichedFunctor.obj b)).hom ≫
          GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (a, b))
  simpa only [Category.assoc, id_tensorHom, tensorHom_id, id_tensorHom_id,
    id_whiskerRight] using congrArg
    (fun z => MonoidalClosed.curry (z ≫
      GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (a, b)))
    (scalarExternalComponentIso_naturality r
      (𝟙 (F.toEnrichedFunctor.obj a)) (𝟙 (X.toEnrichedFunctor.obj b))).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every coefficient retains full naturality in the original second-factor transformation. -/
theorem gradedHomEquiv_naturality_left (M : V) (F : EnrichedFunctorCat V A)
    {X X' : EnrichedFunctorCat V B} (f : X' ⟶ X)
    (Y : EnrichedFunctorCat V (A × B))
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv M F X' Y
        (gradedPrecomp ((Center.ofBraided V).obj M) ((leftFunctor F).map f) t) =
      gradedPrecomp ((Center.ofBraided V).obj M) f (gradedHomEquiv M F X Y t) := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj M)
  intro b
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor (slice Y b).toEnrichedFunctor
  intro a
  rw [gradedHomEquiv_apply_π, gradeFirstComponent_gradedPrecomp,
    leftFunctor_map_component, gradeFirstComponent_gradedPrecomp,
    Category.assoc, gradedHomEquiv_apply_π, ← MonoidalClosed.curry_natural_left]
  change MonoidalClosed.curry
      ((scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
        (X'.toEnrichedFunctor.obj b)).hom ≫ M ◁
          (𝟙 (F.toEnrichedFunctor.obj a) ⊗ₘ component f b) ≫
          GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (a, b)) =
    MonoidalClosed.curry
      (F.toEnrichedFunctor.obj a ◁ (M ◁ component f b) ≫
        (scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
          (X.toEnrichedFunctor.obj b)).hom ≫
          GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (a, b))
  simpa only [Category.assoc, id_tensorHom, id_tensorHom_id] using congrArg
    (fun z => MonoidalClosed.curry (z ≫
      GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (a, b)))
    (scalarExternalComponentIso_naturality (𝟙 M)
      (𝟙 (F.toEnrichedFunctor.obj a)) (component f b)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every coefficient retains the original entire covariant target transformation. -/
theorem gradedHomEquiv_naturality_right (M : V) (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) {Y Z : EnrichedFunctorCat V (A × B)} (q : Y ⟶ Z)
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv M F X Z (gradedPostcomp ((Center.ofBraided V).obj M) t q) =
      gradedPostcomp ((Center.ofBraided V).obj M) (gradedHomEquiv M F X Y t) (rightMap F q) := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj M)
  intro b
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor (slice Z b).toEnrichedFunctor
  intro a
  rw [gradedHomEquiv_apply_π, gradeFirstComponent_gradedPostcomp,
    gradeFirstComponent_gradedPostcomp, Category.assoc, rightMap_component_π,
    reassoc_of% (gradedHomEquiv_apply_π M F X Y t b a), ← MonoidalClosed.curry_natural_right]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Every coefficient retains the original entire contravariant weight transformation. -/
theorem gradedHomEquiv_naturality_source (M : V) {F F' : EnrichedFunctorCat V A}
    (p : F' ⟶ F) (X : EnrichedFunctorCat V B) (Y : EnrichedFunctorCat V (A × B))
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv M F' X Y (gradedPrecomp ((Center.ofBraided V).obj M) (leftWeightMap p X) t) =
      gradedPostcomp ((Center.ofBraided V).obj M) (gradedHomEquiv M F X Y t) (sourceMap p Y) := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj M)
  intro b
  apply Enriched.weightedEnd.hom_ext F'.toEnrichedFunctor (slice Y b).toEnrichedFunctor
  intro a
  let f : F'.toEnrichedFunctor.obj a ⟶ F.toEnrichedFunctor.obj a := component p a
  let q : M ⊗ (F.toEnrichedFunctor.obj a ⊗ X.toEnrichedFunctor.obj b) ⟶
      Y.toEnrichedFunctor.obj (a, b) :=
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (a, b)
  have hpre : GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
      (gradedPrecomp ((Center.ofBraided V).obj M) (leftWeightMap p X) t) (a, b) =
        M ◁ (f ⊗ₘ 𝟙 (X.toEnrichedFunctor.obj b)) ≫ q := by
    exact (gradeFirstComponent_gradedPrecomp ((Center.ofBraided V).obj M)
      (leftWeightMap p X) t (a, b)).trans
      (congrArg (fun z => M ◁ z ≫ q) (leftWeightMap_component p X a b))
  have hn : (scalarExternalComponentIso M (F'.toEnrichedFunctor.obj a)
      (X.toEnrichedFunctor.obj b)).hom ≫ M ◁ (f ⊗ₘ 𝟙 (X.toEnrichedFunctor.obj b)) =
        (f ▷ (M ⊗ X.toEnrichedFunctor.obj b)) ≫
          (scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
            (X.toEnrichedFunctor.obj b)).hom := by
    simpa only [id_tensorHom, tensorHom_id, id_tensorHom_id, id_whiskerRight] using
      (scalarExternalComponentIso_naturality (𝟙 M) f
        (𝟙 (X.toEnrichedFunctor.obj b))).symm
  have hpost : GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
      (gradedPostcomp ((Center.ofBraided V).obj M) (gradedHomEquiv M F X Y t) (sourceMap p Y)) b ≫
        projection F' Y b a =
      GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
        (gradedHomEquiv M F X Y t) b ≫ projection F Y b a ≫
          (MonoidalClosed.pre f).app (Y.toEnrichedFunctor.obj (a, b)) := by
    rw [gradeFirstComponent_gradedPostcomp, Category.assoc, sourceMap_component_π]
  calc
    _ = MonoidalClosed.curry
        ((scalarExternalComponentIso M (F'.toEnrichedFunctor.obj a)
          (X.toEnrichedFunctor.obj b)).hom ≫
            (M ◁ (f ⊗ₘ 𝟙 (X.toEnrichedFunctor.obj b)) ≫ q)) :=
      (gradedHomEquiv_apply_π M F' X Y _ b a).trans
        (congrArg (fun z => MonoidalClosed.curry
          ((scalarExternalComponentIso M (F'.toEnrichedFunctor.obj a)
            (X.toEnrichedFunctor.obj b)).hom ≫ z)) hpre)
    _ = MonoidalClosed.curry ((f ▷ (M ⊗ X.toEnrichedFunctor.obj b)) ≫
        (scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
          (X.toEnrichedFunctor.obj b)).hom ≫ q) := by
      simpa only [Category.assoc] using congrArg
        (fun z => MonoidalClosed.curry (z ≫ q)) hn
    _ = MonoidalClosed.curry
        ((scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
          (X.toEnrichedFunctor.obj b)).hom ≫ q) ≫
          (MonoidalClosed.pre f).app (Y.toEnrichedFunctor.obj (a, b)) :=
      (MonoidalClosed.curry_pre_app f _).symm
    _ = _ := (congrArg (fun z => z ≫
      (MonoidalClosed.pre f).app (Y.toEnrichedFunctor.obj (a, b)))
      (gradedHomEquiv_apply_π M F X Y t b a)).symm
    _ = _ := (Category.assoc _ _ _).trans hpost.symm

omit [HasProducts.{uA} V] [HasEqualizers V] [MonoidalClosed V] in
/-- At the tensor-unit coefficient the original crossing reduces to the original scalar unitor. -/
theorem scalarExternalComponentIso_unit (U K : V) :
    (scalarExternalComponentIso (𝟙_ V) U K).hom ≫ (λ_ (U ⊗ K)).hom = U ◁ (λ_ K).hom := by
  rw [scalarExternalComponentIso_hom, braiding_tensorUnit_right]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary adjunction is exactly the tensor-unit case of the full
coefficient correspondence. -/
theorem gradedHomEquiv_unit (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (t : (leftFunctor F).obj X ⟶ Y) :
    gradedHomEquiv (𝟙_ V) F X Y t = transpose F X Y t := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj (𝟙_ V))
  intro b
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor (slice Y b).toEnrichedFunctor
  intro a
  rw [gradedHomEquiv_apply_π, gradeFirstUnit_component, gradeFirstUnit_component,
    Category.assoc, transpose_component_π, ← MonoidalClosed.curry_natural_left]
  apply congrArg MonoidalClosed.curry
  change (scalarExternalComponentIso (𝟙_ V) (F.toEnrichedFunctor.obj a)
      (X.toEnrichedFunctor.obj b)).hom ≫
      (λ_ (F.toEnrichedFunctor.obj a ⊗ X.toEnrichedFunctor.obj b)).hom ≫ component t (a, b) =
    F.toEnrichedFunctor.obj a ◁ (λ_ (X.toEnrichedFunctor.obj b)).hom ≫ component t (a, b)
  rw [← Category.assoc, scalarExternalComponentIso_unit]

/-- The complete coefficient correspondences form an isomorphism of the
original ambient presheaves. -/
def gradedPresheafIso (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) :
    enrichedNatTransYoneda ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor ⋙
        uliftFunctor.{max uA uB vV, max uA uB vV} ≅
      enrichedNatTransYoneda X.toEnrichedFunctor (rightObject F Y).toEnrichedFunctor ⋙
        uliftFunctor.{max uA uB vV, max uB vV} :=
  NatIso.ofComponents
    (fun M => (Equiv.ulift.trans ((gradedHomEquiv M.unop F X Y).trans Equiv.ulift.symm)).toIso)
    (by
      intro M N r
      apply ConcreteCategory.ext_apply
      intro t
      apply ULift.ext
      change gradedHomEquiv N.unop F X Y
          (GradedNatTrans.regrade ((Center.ofBraided V).map r.unop) t.down) =
        GradedNatTrans.regrade ((Center.ofBraided V).map r.unop)
          (gradedHomEquiv M.unop F X Y t.down)
      exact gradedHomEquiv_regrade r.unop F X Y t.down)

/-- The ambient-presheaf forward map is the whole original coefficient transpose. -/
theorem gradedPresheafIso_hom_app (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (M : V)
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    (gradedPresheafIso F X Y).hom.app (Opposite.op M) (ULift.up t) =
      ULift.up (gradedHomEquiv M F X Y t) := rfl

/-- The ambient-presheaf inverse retains the full actual coefficient and both
inverse component maps. -/
theorem gradedPresheafIso_inv_app (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (M : V)
    (h : GradedNatTrans ((Center.ofBraided V).obj M) X.toEnrichedFunctor
      (rightObject F Y).toEnrichedFunctor) :
    (gradedPresheafIso F X Y).inv.app (Opposite.op M) (ULift.up h) =
      ULift.up ((gradedHomEquiv M F X Y).symm h) := rfl

end Coefficients

end CategoryTheory.EnrichedFunctorCat.ExternalTensorMappingEndAdjunction
