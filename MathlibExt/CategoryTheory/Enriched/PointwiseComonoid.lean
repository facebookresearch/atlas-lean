/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.PointwiseTensor
public import MathlibExt.CategoryTheory.Enriched.ClosedBraidedSelf
public import MathlibExt.CategoryTheory.Enriched.FunctorCategoryIso
public import Mathlib.CategoryTheory.Monoidal.Multifunctor

/-!
# Pointwise tensor from a compatible enriched diagonal

The original index Hom objects carry their actual cocommutative
comultiplications and counits. Compatibility with index identities and
composition is source data. The induced tensor keeps the complete original
enriched diagram actions. No diagram monoidal or model dictionary is an input.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe uA uV vV
open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.PointwiseComonoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

attribute [local instance] Enriched.prodCategory

/-- The complete original compatible index diagonal and counit, before any diagram tensor is
built. -/
structure IndexData where
  /-- The comultiplication of each enriched Hom object, defining the index diagonal's Hom map. -/
  delta : ∀ a b : A, (a ⟶[V] b) ⟶ (a ⟶[V] b) ⊗ (a ⟶[V] b)
  /-- The counit of each enriched Hom object, defining the tensor-unit diagram's Hom action. -/
  epsilon : ∀ a b : A, (a ⟶[V] b) ⟶ 𝟙_ V
  delta_id : ∀ a : A, eId V a ≫ delta a a =
    (λ_ (𝟙_ V)).inv ≫ (eId V a ⊗ₘ eId V a)
  delta_comp : ∀ a b c : A, eComp V a b c ≫ delta a c =
    (delta a b ⊗ₘ delta b c) ≫
      tensorμ (a ⟶[V] b) (a ⟶[V] b) (b ⟶[V] c) (b ⟶[V] c) ≫
        (eComp V a b c ⊗ₘ eComp V a b c)
  epsilon_id : ∀ a : A, eId V a ≫ epsilon a a = 𝟙 (𝟙_ V)
  epsilon_comp : ∀ a b c : A, eComp V a b c ≫ epsilon a c =
    (epsilon a b ⊗ₘ epsilon b c) ≫ (λ_ (𝟙_ V)).hom
  coassoc : ∀ a b : A,
    delta a b ≫ (delta a b ▷ (a ⟶[V] b)) ≫
      (α_ (a ⟶[V] b) (a ⟶[V] b) (a ⟶[V] b)).hom =
    delta a b ≫ ((a ⟶[V] b) ◁ delta a b)
  left_counit : ∀ a b : A,
    delta a b ≫ (epsilon a b ⊗ₘ 𝟙 (a ⟶[V] b)) = (λ_ (a ⟶[V] b)).inv
  right_counit : ∀ a b : A,
    delta a b ≫ (𝟙 (a ⟶[V] b) ⊗ₘ epsilon a b) = (ρ_ (a ⟶[V] b)).inv
  cocomm : ∀ a b : A,
    delta a b ≫ (β_ (a ⟶[V] b) (a ⟶[V] b)).hom = delta a b

/-- The actual original comultiplications construct the compatible enriched diagonal. -/
def diagonal (d : IndexData (V := V) (A := A)) : EnrichedFunctor V A (A × A) where
  obj a := (a, a)
  map := d.delta
  map_id := d.delta_id
  map_comp := d.delta_comp

omit [MonoidalClosed V] in
/-- The compatible diagonal keeps the original index object twice. -/
@[simp]
theorem diagonal_obj (d : IndexData (V := V) (A := A)) (a : A) :
    (diagonal d).obj a = (a, a) := rfl

omit [MonoidalClosed V] in
/-- Its entire Hom map is the original source comultiplication. -/
@[simp]
theorem diagonal_map (d : IndexData (V := V) (A := A)) (a b : A) :
    (diagonal d).map a b = d.delta a b := rfl

/-- The pointwise tensor retains that same source diagonal and its full enriched maps. -/
abbrev tensorObject (d : IndexData (V := V) (A := A)) (F G : EnrichedFunctorCat V A) :=
  (PointwiseTensor.leftTensor (diagonal d) F).obj G

/-- Pointwise values are the exact original coefficient tensors. -/
@[simp]
theorem tensorObject_obj (d : IndexData (V := V) (A := A)) (F G : EnrichedFunctorCat V A) (a : A) :
    (tensorObject d F G).toEnrichedFunctor.obj a =
      F.toEnrichedFunctor.obj a ⊗ G.toEnrichedFunctor.obj a := rfl

private abbrev tmap (X X' Y Y' : V) :=
  (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap X X' Y Y'

/-- The entire pointwise tensor Hom action is the original diagonal followed by the actual
coefficient tensor. -/
private theorem tensorObject_map (d : IndexData (V := V) (A := A)) (F G : EnrichedFunctorCat V A)
    (a b : A) :
    (tensorObject d F G).toEnrichedFunctor.map a b =
      d.delta a b ≫ (F.toEnrichedFunctor.map a b ⊗ₘ G.toEnrichedFunctor.map a b) ≫
        tmap (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b)
          (G.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj b) := rfl

omit [SymmetricCategory V] in
private theorem id_tensor_id_comp (X : V) :
    (eId V X ⊗ₘ eId V X) ≫ eComp V X X X = (λ_ (𝟙_ V)).hom ≫ eId V X := by
  have h := eHomEquiv_comp V (𝟙 X) (𝟙 X)
  simp only [Category.id_comp, eHomEquiv_id] at h
  have h' := congrArg (fun k => (λ_ (𝟙_ V)).hom ≫ k) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'.symm

/-- The original index counits construct the actual pointwise tensor-unit diagram. -/
def tensorUnit (d : IndexData (V := V) (A := A)) : EnrichedFunctorCat V A :=
  ⟨{ obj := fun _ => 𝟙_ V
     map := fun a b => d.epsilon a b ≫ eId V (𝟙_ V)
     map_id := fun a => by rw [← Category.assoc, d.epsilon_id, Category.id_comp]
     map_comp := fun a b c => by
       rw [← Category.assoc, d.epsilon_comp, Category.assoc,
         ← tensorHom_comp_tensorHom_assoc, id_tensor_id_comp] }⟩

/-- The actual tensor unit has the original coefficient unit at every index object. -/
@[simp]
theorem tensorUnit_obj (d : IndexData (V := V) (A := A)) (a : A) :
    (tensorUnit d).toEnrichedFunctor.obj a = 𝟙_ V := rfl

omit [SymmetricCategory V] in
private theorem uncurry_naturality
    {X Y X' Y' H : V} (f : H ⟶ (ihom X).obj Y) (g : H ⟶ (ihom X').obj Y')
    (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ (ihom X).map b = g ≫ (MonoidalClosed.pre a).app Y') :
    MonoidalClosed.uncurry f ≫ b = (a ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry g := by
  have h' := congrArg MonoidalClosed.uncurry h
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app] at h'
  simpa only [tensorHom_id] using h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closed_associator (X X' Y Y' Z Z' : V) :
    (tmap X X' Y Y' ▷ ((ihom Z).obj Z') ≫ tmap (X ⊗ Y) (X' ⊗ Y') Z Z') ≫
      (ihom ((X ⊗ Y) ⊗ Z)).map (α_ X' Y' Z').hom =
    ((α_ ((ihom X).obj X') ((ihom Y).obj Y') ((ihom Z).obj Z')).hom ≫
      ((ihom X).obj X') ◁ tmap Y Y' Z Z' ≫ tmap X X' (Y ⊗ Z) (Y' ⊗ Z')) ≫
      (MonoidalClosed.pre (α_ X Y Z).hom).app (X' ⊗ (Y' ⊗ Z')) := by
  have h := unitGradedNaturality_eq_whisker
    (tmap X X' Y Y' ▷ ((ihom Z).obj Z') ≫ tmap (X ⊗ Y) (X' ⊗ Y') Z Z')
    ((α_ ((ihom X).obj X') ((ihom Y).obj Y') ((ihom Z).obj Z')).hom ≫
      ((ihom X).obj X') ◁ tmap Y Y' Z Z' ≫ tmap X X' (Y ⊗ Z) (Y' ⊗ Z'))
    (α_ X Y Z).hom (α_ X' Y' Z').hom
    ((MonoidalClosed.enrichedMonoidalCategoryDataSelf V).associatorNaturality X X' Y Y' Z Z')
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem left_associator_form (d : IndexData (V := V) (A := A))
    (F G H : EnrichedFunctorCat V A) (a b : A) :
    (tensorObject d (tensorObject d F G) H).toEnrichedFunctor.map a b =
      d.delta a b ≫ (d.delta a b ▷ (a ⟶[V] b)) ≫
        ((F.toEnrichedFunctor.map a b ⊗ₘ G.toEnrichedFunctor.map a b) ⊗ₘ
          H.toEnrichedFunctor.map a b) ≫
        (tmap (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b)
          (G.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj b) ▷
            ((ihom (H.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj b))) ≫
        tmap (F.toEnrichedFunctor.obj a ⊗ G.toEnrichedFunctor.obj a)
          (F.toEnrichedFunctor.obj b ⊗ G.toEnrichedFunctor.obj b)
          (H.toEnrichedFunctor.obj a) (H.toEnrichedFunctor.obj b) := by
  rw [tensorObject_map, tensorObject_map]
  simp only [tensorObject_obj]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  erw [Category.comp_id (H.toEnrichedFunctor.map a b)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem right_associator_form (d : IndexData (V := V) (A := A))
    (F G H : EnrichedFunctorCat V A) (a b : A) :
    (tensorObject d F (tensorObject d G H)).toEnrichedFunctor.map a b =
      d.delta a b ≫ (d.delta a b ▷ (a ⟶[V] b)) ≫
        ((F.toEnrichedFunctor.map a b ⊗ₘ G.toEnrichedFunctor.map a b) ⊗ₘ
          H.toEnrichedFunctor.map a b) ≫
        (α_ ((ihom (F.toEnrichedFunctor.obj a)).obj (F.toEnrichedFunctor.obj b))
          ((ihom (G.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj b))
          ((ihom (H.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj b))).hom ≫
        ((ihom (F.toEnrichedFunctor.obj a)).obj (F.toEnrichedFunctor.obj b)) ◁
          tmap (G.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj b)
            (H.toEnrichedFunctor.obj a) (H.toEnrichedFunctor.obj b) ≫
        tmap (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b)
          (G.toEnrichedFunctor.obj a ⊗ H.toEnrichedFunctor.obj a)
          (G.toEnrichedFunctor.obj b ⊗ H.toEnrichedFunctor.obj b) := by
  rw [tensorObject_map, tensorObject_map]
  simp only [tensorObject_obj]
  erw [associator_naturality_assoc]
  have hc := congrArg (fun k => k ≫
    (F.toEnrichedFunctor.map a b ⊗ₘ
      (G.toEnrichedFunctor.map a b ⊗ₘ H.toEnrichedFunctor.map a b)) ≫
    ((ihom (F.toEnrichedFunctor.obj a)).obj (F.toEnrichedFunctor.obj b)) ◁
      tmap (G.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj b)
        (H.toEnrichedFunctor.obj a) (H.toEnrichedFunctor.obj b) ≫
    tmap (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b)
      (G.toEnrichedFunctor.obj a ⊗ H.toEnrichedFunctor.obj a)
      (G.toEnrichedFunctor.obj b ⊗ H.toEnrichedFunctor.obj b)) (d.coassoc a b)
  simp only [Category.assoc] at hc
  rw [hc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp]
  erw [Category.comp_id (F.toEnrichedFunctor.map a b)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual coefficient associator is natural on every entire original index Hom object. -/
theorem associator_naturality (d : IndexData (V := V) (A := A))
    (F G H : EnrichedFunctorCat V A) (a b : A) :
    MonoidalClosed.uncurry
      ((tensorObject d (tensorObject d F G) H).toEnrichedFunctor.map a b) ≫
        (α_ (F.toEnrichedFunctor.obj b) (G.toEnrichedFunctor.obj b)
          (H.toEnrichedFunctor.obj b)).hom =
    ((α_ (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
      (H.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry
        ((tensorObject d F (tensorObject d G H)).toEnrichedFunctor.map a b) := by
  apply uncurry_naturality
  rw [left_associator_form, right_associator_form]
  let S := d.delta a b ≫ (d.delta a b ▷ (a ⟶[V] b)) ≫
    ((F.toEnrichedFunctor.map a b ⊗ₘ G.toEnrichedFunctor.map a b) ⊗ₘ
      H.toEnrichedFunctor.map a b)
  have h := congrArg (fun k => S ≫ k)
    (closed_associator (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b)
      (G.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj b)
      (H.toEnrichedFunctor.obj a) (H.toEnrichedFunctor.obj b))
  simpa only [S, tensorObject_obj, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closed_leftUnitor (X X' : V) :
    ((λ_ ((ihom X).obj X')).inv ≫ (eId V (𝟙_ V) ⊗ₘ 𝟙 ((ihom X).obj X')) ≫
      tmap (𝟙_ V) (𝟙_ V) X X') ≫ (ihom (𝟙_ V ⊗ X)).map (λ_ X').hom =
    (MonoidalClosed.pre (λ_ X).hom).app X' := by
  have h := unitGradedNaturality_eq_whisker
    ((λ_ ((ihom X).obj X')).inv ≫ (eId V (𝟙_ V) ⊗ₘ 𝟙 ((ihom X).obj X')) ≫
      tmap (𝟙_ V) (𝟙_ V) X X') (𝟙 ((ihom X).obj X'))
    (λ_ X).hom (λ_ X').hom
    ((MonoidalClosed.enrichedMonoidalCategoryDataSelf V).leftUnitorNaturality X X')
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closed_rightUnitor (X X' : V) :
    ((ρ_ ((ihom X).obj X')).inv ≫ (𝟙 ((ihom X).obj X') ⊗ₘ eId V (𝟙_ V)) ≫
      tmap X X' (𝟙_ V) (𝟙_ V)) ≫ (ihom (X ⊗ 𝟙_ V)).map (ρ_ X').hom =
    (MonoidalClosed.pre (ρ_ X).hom).app X' := by
  have h := unitGradedNaturality_eq_whisker
    ((ρ_ ((ihom X).obj X')).inv ≫ (𝟙 ((ihom X).obj X') ⊗ₘ eId V (𝟙_ V)) ≫
      tmap X X' (𝟙_ V) (𝟙_ V)) (𝟙 ((ihom X).obj X'))
    (ρ_ X).hom (ρ_ X').hom
    ((MonoidalClosed.enrichedMonoidalCategoryDataSelf V).rightUnitorNaturality X X')
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem left_unitor_form (d : IndexData (V := V) (A := A))
    (F : EnrichedFunctorCat V A) (a b : A) :
    (tensorObject d (tensorUnit d) F).toEnrichedFunctor.map a b =
      F.toEnrichedFunctor.map a b ≫
        (λ_ ((ihom (F.toEnrichedFunctor.obj a)).obj (F.toEnrichedFunctor.obj b))).inv ≫
        (eId V (𝟙_ V) ⊗ₘ 𝟙 ((ihom (F.toEnrichedFunctor.obj a)).obj (F.toEnrichedFunctor.obj b))) ≫
          tmap (𝟙_ V) (𝟙_ V) (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b) := by
  rw [tensorObject_map]
  change d.delta a b ≫ ((d.epsilon a b ≫ eId V (𝟙_ V)) ⊗ₘ F.toEnrichedFunctor.map a b) ≫
    tmap (𝟙_ V) (𝟙_ V) (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b) = _
  erw [leftUnitor_inv_naturality_assoc, ← d.left_counit]
  simp only [← id_tensorHom, Category.assoc, tensorHom_comp_tensorHom_assoc,
    Category.id_comp]
  exact congrArg (fun k => d.delta a b ≫ ((d.epsilon a b ≫ eId V (𝟙_ V)) ⊗ₘ k) ≫
    tmap (𝟙_ V) (𝟙_ V) (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b))
      (Category.comp_id (F.toEnrichedFunctor.map a b)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem right_unitor_form (d : IndexData (V := V) (A := A))
    (F : EnrichedFunctorCat V A) (a b : A) :
    (tensorObject d F (tensorUnit d)).toEnrichedFunctor.map a b =
      F.toEnrichedFunctor.map a b ≫
        (ρ_ ((ihom (F.toEnrichedFunctor.obj a)).obj (F.toEnrichedFunctor.obj b))).inv ≫
        (𝟙 ((ihom (F.toEnrichedFunctor.obj a)).obj (F.toEnrichedFunctor.obj b)) ⊗ₘ eId V (𝟙_ V)) ≫
          tmap (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b) (𝟙_ V) (𝟙_ V) := by
  rw [tensorObject_map]
  change d.delta a b ≫ (F.toEnrichedFunctor.map a b ⊗ₘ (d.epsilon a b ≫ eId V (𝟙_ V))) ≫
    tmap (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b) (𝟙_ V) (𝟙_ V) = _
  erw [rightUnitor_inv_naturality_assoc, ← d.right_counit]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  erw [Category.assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp]
  exact congrArg (fun k => d.delta a b ≫ (k ⊗ₘ (d.epsilon a b ≫ eId V (𝟙_ V))) ≫
    tmap (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b) (𝟙_ V) (𝟙_ V))
      (Category.comp_id (F.toEnrichedFunctor.map a b)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chosen original left unitor is natural for the entire index Hom action. -/
theorem leftUnitor_naturality (d : IndexData (V := V) (A := A))
    (F : EnrichedFunctorCat V A) (a b : A) :
    MonoidalClosed.uncurry ((tensorObject d (tensorUnit d) F).toEnrichedFunctor.map a b) ≫
      (λ_ (F.toEnrichedFunctor.obj b)).hom =
    ((λ_ (F.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  apply uncurry_naturality
  rw [left_unitor_form]
  have h := congrArg (fun k => F.toEnrichedFunctor.map a b ≫ k)
    (closed_leftUnitor (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b))
  simpa only [tensorObject_obj, tensorUnit_obj, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original right unitor retains the full original enriched action square. -/
theorem rightUnitor_naturality (d : IndexData (V := V) (A := A))
    (F : EnrichedFunctorCat V A) (a b : A) :
    MonoidalClosed.uncurry ((tensorObject d F (tensorUnit d)).toEnrichedFunctor.map a b) ≫
      (ρ_ (F.toEnrichedFunctor.obj b)).hom =
    ((ρ_ (F.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  apply uncurry_naturality
  rw [right_unitor_form]
  have h := congrArg (fun k => F.toEnrichedFunctor.map a b ≫ k)
    (closed_rightUnitor (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b))
  simpa only [tensorObject_obj, tensorUnit_obj, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closed_braiding (X X' Y Y' : V) :
    tmap X X' Y Y' ≫ (ihom (X ⊗ Y)).map (β_ X' Y').hom =
    ((β_ ((ihom X).obj X') ((ihom Y).obj Y')).hom ≫ tmap Y Y' X X') ≫
      (MonoidalClosed.pre (β_ X Y).hom).app (Y' ⊗ X') := by
  have h := unitGradedNaturality_eq_whisker (tmap X X' Y Y')
    ((β_ ((ihom X).obj X') ((ihom Y).obj Y')).hom ≫ tmap Y Y' X X')
    (β_ X Y).hom (β_ X' Y').hom
    ((MonoidalClosed.enrichedBraidedMonoidalCategoryDataSelf V).braidingNaturality X X' Y Y')
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original coefficient symmetry is natural on the entire cocommutative index Hom. -/
theorem braiding_naturality (d : IndexData (V := V) (A := A))
    (F G : EnrichedFunctorCat V A) (a b : A) :
    MonoidalClosed.uncurry ((tensorObject d F G).toEnrichedFunctor.map a b) ≫
      (β_ (F.toEnrichedFunctor.obj b) (G.toEnrichedFunctor.obj b)).hom =
    ((β_ (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry ((tensorObject d G F).toEnrichedFunctor.map a b) := by
  apply uncurry_naturality
  rw [tensorObject_map, tensorObject_map]
  simp only [tensorObject_obj]
  let S := d.delta a b ≫ (F.toEnrichedFunctor.map a b ⊗ₘ G.toEnrichedFunctor.map a b)
  have h := congrArg (fun k => S ≫ k)
    (closed_braiding (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b)
      (G.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj b))
  dsimp only [S] at h
  simp only [Category.assoc] at h
  erw [braiding_naturality_assoc,
    ← Category.assoc (d.delta a b) ((β_ (a ⟶[V] b) (a ⟶[V] b)).hom), d.cocomm a b] at h
  simpa only [Category.assoc] using h

/-- The tensor acts on the actual full unit-graded input transformations. -/
def tensorMap (d : IndexData (V := V) (A := A))
    {F F' G G' : EnrichedFunctorCat V A} (f : F ⟶ F') (g : G ⟶ G') :
    tensorObject d F G ⟶ tensorObject d F' G' :=
  restrictionMap (diagonal d) (EnrichedFunctor.externalMap f g)

/-- Each original tensor map has the complete original coefficient tensor component. -/
theorem tensorMap_component (d : IndexData (V := V) (A := A))
    {F F' G G' : EnrichedFunctorCat V A} (f : F ⟶ F') (g : G ⟶ G') (a : A) :
    component (tensorMap d f g) a = component f a ⊗ₘ component g a := by
  rw [tensorMap]
  erw [restrictionMap_component]
  exact EnrichedFunctor.externalMap_component f g (a, a)

/-- The associator retains the actual selected coefficient associators and full Hom naturality. -/
def associatorIso (d : IndexData (V := V) (A := A)) (F G H : EnrichedFunctorCat V A) :
    tensorObject d (tensorObject d F G) H ≅ tensorObject d F (tensorObject d G H) :=
  isoOfComponents _ _ (fun a => α_ (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
    (H.toEnrichedFunctor.obj a)) (associator_naturality d F G H)

/-- The genuine left unitor uses the original coefficient left unitor maps. -/
def leftUnitorIso (d : IndexData (V := V) (A := A)) (F : EnrichedFunctorCat V A) :
    tensorObject d (tensorUnit d) F ≅ F :=
  isoOfComponents _ _ (fun a => λ_ (F.toEnrichedFunctor.obj a)) (leftUnitor_naturality d F)

/-- The genuine right unitor uses the same original coefficient right unitor maps. -/
def rightUnitorIso (d : IndexData (V := V) (A := A)) (F : EnrichedFunctorCat V A) :
    tensorObject d F (tensorUnit d) ≅ F :=
  isoOfComponents _ _ (fun a => ρ_ (F.toEnrichedFunctor.obj a)) (rightUnitor_naturality d F)

/-- The genuine braiding is the original coefficient braiding at every unchanged index object. -/
def braidingIso (d : IndexData (V := V) (A := A)) (F G : EnrichedFunctorCat V A) :
    tensorObject d F G ≅ tensorObject d G F :=
  isoOfComponents _ _ (fun a => β_ (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a))
    (braiding_naturality d F G)

theorem associator_hom_component (d : IndexData (V := V) (A := A))
    (F G H : EnrichedFunctorCat V A) (a : A) :
    component (associatorIso d F G H).hom a =
      (α_ (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
        (H.toEnrichedFunctor.obj a)).hom :=
  isoOfComponents_hom_component _ _ _ _ a

theorem associator_inv_component (d : IndexData (V := V) (A := A))
    (F G H : EnrichedFunctorCat V A) (a : A) :
    component (associatorIso d F G H).inv a =
      (α_ (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
        (H.toEnrichedFunctor.obj a)).inv :=
  isoOfComponents_inv_component _ _ _ _ a

theorem leftUnitor_hom_component (d : IndexData (V := V) (A := A))
    (F : EnrichedFunctorCat V A) (a : A) :
    component (leftUnitorIso d F).hom a = (λ_ (F.toEnrichedFunctor.obj a)).hom :=
  isoOfComponents_hom_component _ _ _ _ a

theorem rightUnitor_hom_component (d : IndexData (V := V) (A := A))
    (F : EnrichedFunctorCat V A) (a : A) :
    component (rightUnitorIso d F).hom a = (ρ_ (F.toEnrichedFunctor.obj a)).hom :=
  isoOfComponents_hom_component _ _ _ _ a

/-- The actual source diagonal constructs every tensor and original constraint map. -/
@[instance_reducible]
def monoidalStruct (d : IndexData (V := V) (A := A)) :
    MonoidalCategoryStruct (EnrichedFunctorCat V A) where
  tensorObj := tensorObject d
  tensorHom := tensorMap d
  whiskerLeft F _ _ q := tensorMap d (𝟙 F) q
  whiskerRight q G := tensorMap d q (𝟙 G)
  tensorUnit := tensorUnit d
  associator := associatorIso d
  leftUnitor := leftUnitorIso d
  rightUnitor := rightUnitorIso d

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coassociativity and counit compatibility construct the full pointwise monoidal category. -/
@[instance_reducible]
def monoidalCategory (d : IndexData (V := V) (A := A)) :
    MonoidalCategory (EnrichedFunctorCat V A) := by
  letI := monoidalStruct d
  refine MonoidalCategory.ofTensorHom
    (id_tensorHom_id := ?_) (tensorHom_comp_tensorHom := ?_)
    (pentagon := ?_) (triangle := ?_)
    (leftUnitor_naturality := ?_) (rightUnitor_naturality := ?_)
    (associator_naturality := ?_)
  · intro F G
    apply hom_ext
    intro a
    change component (tensorMap d (𝟙 F) (𝟙 G)) a = component (𝟙 (tensorObject d F G)) a
    rw [tensorMap_component, component_id, component_id, component_id, id_tensorHom_id]
    simp only [tensorObject_obj]
  · intro F F' F'' G G' G'' f g f' g'
    apply hom_ext
    intro a
    change component (tensorMap d f g ≫ tensorMap d f' g') a =
      component (tensorMap d (f ≫ f') (g ≫ g')) a
    rw [component_comp, tensorMap_component, tensorMap_component, tensorMap_component,
      component_comp, component_comp, tensorHom_comp_tensorHom]
  · intro F G H F' G' H' f g h
    apply hom_ext
    intro a
    change component (tensorMap d (tensorMap d f g) h ≫ (associatorIso d F' G' H').hom) a =
      component ((associatorIso d F G H).hom ≫ tensorMap d f (tensorMap d g h)) a
    simp only [component_comp, tensorMap_component, associator_hom_component]
    exact MonoidalCategory.associator_naturality _ _ _
  · intro F G q
    apply hom_ext
    intro a
    change component (tensorMap d (𝟙 (tensorUnit d)) q ≫ (leftUnitorIso d G).hom) a =
      component ((leftUnitorIso d F).hom ≫ q) a
    simp only [component_comp, tensorMap_component, component_id, leftUnitor_hom_component,
      tensorUnit_obj, id_tensorHom]
    exact MonoidalCategory.leftUnitor_naturality _
  · intro F G q
    apply hom_ext
    intro a
    change component (tensorMap d q (𝟙 (tensorUnit d)) ≫ (rightUnitorIso d G).hom) a =
      component ((rightUnitorIso d F).hom ≫ q) a
    simp only [component_comp, tensorMap_component, component_id, rightUnitor_hom_component,
      tensorUnit_obj, tensorHom_id]
    exact MonoidalCategory.rightUnitor_naturality _
  · intro F G H K
    apply hom_ext
    intro a
    change component ((tensorMap d (associatorIso d F G H).hom (𝟙 K)) ≫
      (associatorIso d F (tensorObject d G H) K).hom ≫
      tensorMap d (𝟙 F) (associatorIso d G H K).hom) a =
      component ((associatorIso d (tensorObject d F G) H K).hom ≫
        (associatorIso d F G (tensorObject d H K)).hom) a
    simp only [component_comp, tensorMap_component, component_id, associator_hom_component,
      tensorObject_obj, tensorHom_id, id_tensorHom]
    exact pentagon _ _ _ _
  · intro F G
    apply hom_ext
    intro a
    change component ((associatorIso d F (tensorUnit d) G).hom ≫
      tensorMap d (𝟙 F) (leftUnitorIso d G).hom) a =
      component (tensorMap d (rightUnitorIso d F).hom (𝟙 G)) a
    simp only [component_comp, tensorMap_component, component_id, associator_hom_component,
      leftUnitor_hom_component, rightUnitor_hom_component, tensorUnit_obj,
      tensorHom_id, id_tensorHom]
    exact triangle _ _

/-- The constructed diagram tensor is the literal original diagonal restriction. -/
theorem monoidal_tensorObject (d : IndexData (V := V) (A := A))
    (F G : EnrichedFunctorCat V A) :
    letI := monoidalCategory d
    F ⊗ G = tensorObject d F G := rfl

/-- The complete tensor action retains the original Hom comultiplication and coefficient tensor. -/
theorem tensorObject_fullHom (d : IndexData (V := V) (A := A))
    (F G : EnrichedFunctorCat V A) (a b : A) :
    (tensorObject d F G).toEnrichedFunctor.map a b =
      d.delta a b ≫ (F.toEnrichedFunctor.map a b ⊗ₘ G.toEnrichedFunctor.map a b) ≫
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
          (F.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj b)
          (G.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj b) := rfl

/-- The complete unit action retains the original Hom counit. -/
theorem tensorUnit_fullHom (d : IndexData (V := V) (A := A)) (a b : A) :
    (tensorUnit d).toEnrichedFunctor.map a b = d.epsilon a b ≫ eId V (𝟙_ V) := rfl

/-- The original coefficient braiding is the entire diagram braiding component. -/
theorem braiding_hom_component (d : IndexData (V := V) (A := A))
    (F G : EnrichedFunctorCat V A) (a : A) :
    component (braidingIso d F G).hom a =
      (β_ (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)).hom :=
  isoOfComponents_hom_component _ _ _ _ a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source cocommutativity constructs a braiding on the actual pointwise tensor. -/
@[instance_reducible]
def braidedCategory (d : IndexData (V := V) (A := A)) :
    letI := monoidalCategory d
    BraidedCategory (EnrichedFunctorCat V A) := by
  letI := monoidalCategory d
  refine
    { braiding := braidingIso d
      braiding_naturality_right := ?_
      braiding_naturality_left := ?_
      hexagon_forward := ?_
      hexagon_reverse := ?_ }
  · intro F G H q
    apply hom_ext
    intro a
    change component (tensorMap d (𝟙 F) q ≫ (braidingIso d F H).hom) a =
      component ((braidingIso d F G).hom ≫ tensorMap d q (𝟙 F)) a
    simp only [component_comp, tensorMap_component, component_id, braiding_hom_component,
      id_tensorHom, tensorHom_id]
    exact BraidedCategory.braiding_naturality_right _ _
  · intro F G q H
    apply hom_ext
    intro a
    change component (tensorMap d q (𝟙 H) ≫ (braidingIso d G H).hom) a =
      component ((braidingIso d F H).hom ≫ tensorMap d (𝟙 H) q) a
    simp only [component_comp, tensorMap_component, component_id, braiding_hom_component,
      id_tensorHom, tensorHom_id]
    exact BraidedCategory.braiding_naturality_left _ _
  · intro F G H
    apply hom_ext
    intro a
    change component ((associatorIso d F G H).hom ≫
      (braidingIso d F (tensorObject d G H)).hom ≫
      (associatorIso d G H F).hom) a =
      component (tensorMap d (braidingIso d F G).hom (𝟙 H) ≫
        (associatorIso d G F H).hom ≫
        tensorMap d (𝟙 G) (braidingIso d F H).hom) a
    simp only [component_comp, tensorMap_component, component_id, associator_hom_component,
      braiding_hom_component, tensorObject_obj, tensorHom_id, id_tensorHom]
    exact BraidedCategory.hexagon_forward _ _ _
  · intro F G H
    apply hom_ext
    intro a
    change component ((associatorIso d F G H).inv ≫
      (braidingIso d (tensorObject d F G) H).hom ≫
      (associatorIso d H F G).inv) a =
      component (tensorMap d (𝟙 F) (braidingIso d G H).hom ≫
        (associatorIso d F H G).inv ≫
        tensorMap d (braidingIso d F H).hom (𝟙 G)) a
    simp only [component_comp, tensorMap_component, component_id, associator_inv_component,
      braiding_hom_component, tensorObject_obj, tensorHom_id, id_tensorHom]
    exact BraidedCategory.hexagon_reverse _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coefficient symmetry gives symmetry of the constructed original diagram tensor. -/
@[instance_reducible]
def symmetricCategory (d : IndexData (V := V) (A := A)) :
    letI := monoidalCategory d
    SymmetricCategory (EnrichedFunctorCat V A) := by
  letI := monoidalCategory d
  refine { toBraidedCategory := braidedCategory d, symmetry := ?_ }
  intro F G
  apply hom_ext
  intro a
  change component ((braidingIso d F G).hom ≫
    (braidingIso d G F).hom) a = component (𝟙 (tensorObject d F G)) a
  simp only [component_comp, braiding_hom_component, component_id, tensorObject_obj]
  exact SymmetricCategory.symmetry _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The monoidal left tensor keeps the complete original external-tensor restriction functor. -/
def leftTensorIso (d : IndexData (V := V) (A := A)) (F : EnrichedFunctorCat V A) :
    letI := monoidalCategory d
    MonoidalCategory.tensorLeft F ≅ PointwiseTensor.leftTensor (diagonal d) F := by
  letI := monoidalCategory d
  refine NatIso.ofComponents (fun G => Iso.refl (tensorObject d F G)) ?_
  intro G H q
  simp only [Iso.refl_hom]
  apply hom_ext
  intro a
  erw [component_comp, component_comp, component_id, component_id]
  simp only [Category.comp_id, Category.id_comp]
  erw [PointwiseTensor.leftTensor_map_component]

variable [HasProducts.{uA} V] [HasEqualizers V]

/-- The actual pointwise tensor is closed by its original enriched Kan/end right adjoint. -/
@[instance_reducible]
def monoidalClosed (d : IndexData (V := V) (A := A)) :
    letI := monoidalCategory d
    MonoidalClosed (EnrichedFunctorCat V A) := by
  letI := monoidalCategory d
  exact
    { closed := fun F =>
        { rightAdj := PointwiseTensor.rightTensor (diagonal d) F
          adj := (PointwiseTensor.adjunction (diagonal d) F).ofNatIsoLeft
            (leftTensorIso d F).symm } }

/-- The constructed internal Hom is the complete original right Kan and weighted end composite. -/
theorem ihom_eq (d : IndexData (V := V) (A := A)) (F : EnrichedFunctorCat V A) :
    letI := monoidalCategory d
    letI := monoidalClosed d
    ihom F = PointwiseTensor.rightTensor (diagonal d) F := rfl

/-- Every binary internal Hom value is the actual external mapping end of the original Kan value. -/
theorem ihom_obj (d : IndexData (V := V) (A := A)) (F G : EnrichedFunctorCat V A) (a : A) :
    letI := monoidalCategory d
    letI := monoidalClosed d
    ((ihom F).obj G).toEnrichedFunctor.obj a =
      ExternalTensorMappingEndAdjunction.mappingObject F ((rightKan (diagonal d)).obj G) a := rfl

end CategoryTheory.EnrichedFunctorCat.PointwiseComonoid
