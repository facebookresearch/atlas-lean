/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Canonical trace in symmetric right rigid monoidal categories

The trace structure records naturality, dinaturality, both vanishing axioms,
superposing and yanking, with associators and unitors explicit. The proved
construction equips a symmetric right rigid category with this structure;
left duals need not be supplied. No trace is asserted to exist on an arbitrary
symmetric category.
The feedback operation uses a right dual, evaluation, coevaluation and the
symmetry. Independence of the exact pairing permits the unit and tensor
axioms to use convenient pairings instead of requiring chosen duals to agree
definitionally. No analytic or fixed-point interpretation is assumed.

Source: Joyal, Street and Verity, Traced monoidal categories (1996),
https://doi.org/10.1017/S0305004100074338, specialized to the symmetric case.
-/
@[expose] public section
universe v u
namespace CategoryTheory
open MonoidalCategory
open scoped MonoidalCategory

/-- A trace satisfying the Joyal–Street–Verity symmetric trace axioms. -/
structure SymmetricTrace (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C] where
  /-- Feedback over the right tensor factor. -/
  trace : ∀ {X Y U : C}, (X ⊗ U ⟶ Y ⊗ U) → (X ⟶ Y)
  /-- Naturality in the input and output objects. -/
  naturality : ∀ {X X' Y Y' U : C} (f : X ⊗ U ⟶ Y ⊗ U)
    (g : X' ⟶ X) (h : Y ⟶ Y'),
    trace ((g ⊗ₘ 𝟙 U) ≫ f ≫ (h ⊗ₘ 𝟙 U)) = g ≫ trace f ≫ h
  /-- Sliding a morphism around the feedback loop. -/
  dinaturality : ∀ {X Y U V : C} (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U),
    trace (f ≫ (𝟙 Y ⊗ₘ g)) = trace ((𝟙 X ⊗ₘ g) ≫ f)
  /-- Tracing over the tensor unit removes the unitors. -/
  vanishing_unit : ∀ {X Y : C} (f : X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C),
    trace f = (ρ_ X).inv ≫ f ≫ (ρ_ Y).hom
  /-- Tracing two factors agrees with tracing them successively. -/
  vanishing_tensor : ∀ {X Y U V : C} (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)),
    trace f = trace (trace ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv))
  /-- A morphism on an untouched factor may be superposed. -/
  superposing : ∀ {X Y U W Z : C} (f : X ⊗ U ⟶ Y ⊗ U) (g : W ⟶ Z),
    trace ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫ (α_ Z Y U).inv) = g ⊗ₘ trace f
  /-- Feedback through the symmetry is the identity. -/
  yanking : ∀ X : C, trace (β_ X X).hom = 𝟙 X


namespace SymmetricTrace

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C]

/-- Close the right factor using a specified exact pairing. -/
def traceOfPairing {X Y U : C} (D : C) [ExactPairing U D]
    (f : X ⊗ U ⟶ Y ⊗ U) : X ⟶ Y :=
  (ρ_ X).inv ≫ X ◁ η_ U D ≫ (α_ X U D).inv ≫ f ▷ D ≫
    (α_ Y U D).hom ≫ Y ◁ (β_ U D).hom ≫ Y ◁ ε_ U D ≫ (ρ_ Y).hom

/-- Naturality in the factors outside the feedback loop. -/
theorem traceOfPairing_naturality {X X' Y Y' U : C} (D : C) [ExactPairing U D]
    (f : X ⊗ U ⟶ Y ⊗ U) (g : X' ⟶ X) (h : Y ⟶ Y') :
    traceOfPairing D ((g ⊗ₘ 𝟙 U) ≫ f ≫ (h ⊗ₘ 𝟙 U)) =
      g ≫ traceOfPairing D f ≫ h := by
  simp only [traceOfPairing, comp_whiskerRight, tensorHom_id, Category.assoc]
  rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc]
  simp

/-- Tensoring an unrelated morphism commutes with feedback. -/
theorem traceOfPairing_superposing {X Y U W Z : C} (D : C) [ExactPairing U D]
    (f : X ⊗ U ⟶ Y ⊗ U) (g : W ⟶ Z) :
    traceOfPairing D ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫ (α_ Z Y U).inv) =
      g ⊗ₘ traceOfPairing D f := by
  have inner : traceOfPairing D ((α_ Z X U).hom ≫ Z ◁ f ≫
      (α_ Z Y U).inv) = Z ◁ traceOfPairing D f := by
    unfold traceOfPairing
    monoidal
  calc
    _ = traceOfPairing D (((g ▷ X) ⊗ₘ 𝟙 U) ≫
        ((α_ Z X U).hom ≫ Z ◁ f ≫ (α_ Z Y U).inv) ≫ 𝟙 _) := by
      congr 1
      simp [tensorHom_def]
    _ = (g ▷ X) ≫ traceOfPairing D
        ((α_ Z X U).hom ≫ Z ◁ f ≫ (α_ Z Y U).inv) ≫ 𝟙 _ := by
      simpa using traceOfPairing_naturality D
        ((α_ Z X U).hom ≫ Z ◁ f ≫ (α_ Z Y U).inv) (g ▷ X) (𝟙 (Z ⊗ Y))
    _ = _ := by rw [inner]; simp [tensorHom_def]

/-- The standard unit pairing gives the unitor composite. -/
theorem traceOfPairing_unit {X Y : C} (f : X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C) :
    traceOfPairing (𝟙_ C) f = (ρ_ X).inv ≫ f ≫ (ρ_ Y).hom := by
  change (ρ_ X).inv ≫ X ◁ (ρ_ (𝟙_ C)).inv ≫ (α_ X _ _).inv ≫ f ▷ _ ≫
    (α_ Y _ _).hom ≫ Y ◁ (β_ (𝟙_ C) (𝟙_ C)).hom ≫
    Y ◁ (ρ_ (𝟙_ C)).hom ≫ (ρ_ Y).hom = _
  rw [braiding_tensorUnit_left]
  monoidal

/-- Closing a symmetry straightens to the identity. -/
theorem traceOfPairing_yanking (X D : C) [ExactPairing X D] :
    traceOfPairing D (β_ X X).hom = 𝟙 X := by
  calc
    _ = (ρ_ X).inv ≫ (X ◁ η_ X D ≫ (β_ X (X ⊗ D)).hom) ≫
        (α_ X D X).hom ≫ X ◁ ε_ X D ≫ (ρ_ X).hom := by
      simp only [traceOfPairing, BraidedCategory.braiding_tensor_right_hom]
      monoidal
    _ = (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom ≫ η_ X D ▷ X ≫
        (α_ X D X).hom ≫ X ◁ ε_ X D ≫ (ρ_ X).hom := by
      rw [BraidedCategory.braiding_naturality_right]
      simp only [Category.assoc]
    _ = _ := by
      rw [braiding_tensorUnit_right]
      simp [ExactPairing.evaluation_coevaluation_assoc]

/-- Sliding a morphism and its dual across feedback. -/
theorem traceOfPairing_slide {X Y U V D E : C} [ExactPairing U D]
    [ExactPairing V E] (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U) (k : D ⟶ E)
    (hη : η_ U D ≫ U ◁ k = η_ V E ≫ g ▷ E)
    (hε : k ▷ V ≫ ε_ V E = D ◁ g ≫ ε_ U D) :
    traceOfPairing D (f ≫ Y ◁ g) = traceOfPairing E (X ◁ g ≫ f) := by
  have cap : g ▷ D ≫ (β_ U D).hom ≫ ε_ U D =
      V ◁ k ≫ (β_ V E).hom ≫ ε_ V E := by
    rw [BraidedCategory.braiding_naturality_left_assoc, ← hε,
      ← BraidedCategory.braiding_naturality_right_assoc]
  calc
    _ = 𝟙 X ⊗≫ X ◁ η_ U D ⊗≫ f ▷ D ⊗≫
        Y ◁ (g ▷ D ≫ (β_ U D).hom ≫ ε_ U D) ⊗≫ 𝟙 Y := by
      unfold traceOfPairing
      monoidal
    _ = 𝟙 X ⊗≫ X ◁ η_ U D ⊗≫ f ▷ D ⊗≫
        Y ◁ (V ◁ k ≫ (β_ V E).hom ≫ ε_ V E) ⊗≫ 𝟙 Y := by rw [cap]
    _ = 𝟙 X ⊗≫ X ◁ η_ U D ⊗≫
        (f ▷ D ≫ (Y ⊗ V) ◁ k) ⊗≫
        Y ◁ ((β_ V E).hom ≫ ε_ V E) ⊗≫ 𝟙 Y := by monoidal
    _ = 𝟙 X ⊗≫ X ◁ η_ U D ⊗≫
        ((X ⊗ U) ◁ k ≫ f ▷ E) ⊗≫
        Y ◁ ((β_ V E).hom ≫ ε_ V E) ⊗≫ 𝟙 Y := by rw [← whisker_exchange]
    _ = 𝟙 X ⊗≫ X ◁ (η_ U D ≫ U ◁ k) ⊗≫ f ▷ E ⊗≫
        Y ◁ ((β_ V E).hom ≫ ε_ V E) ⊗≫ 𝟙 Y := by monoidal
    _ = 𝟙 X ⊗≫ X ◁ (η_ V E ≫ g ▷ E) ⊗≫ f ▷ E ⊗≫
        Y ◁ ((β_ V E).hom ≫ ε_ V E) ⊗≫ 𝟙 Y := by rw [hη]
    _ = _ := by unfold traceOfPairing; monoidal

/-- Feedback is independent of the chosen right dual and exact pairing. -/
theorem traceOfPairing_independent {X Y U D E : C}
    [p : ExactPairing U D] [q : ExactPairing U E] (f : X ⊗ U ⟶ Y ⊗ U) :
    traceOfPairing D f = traceOfPairing E f := by
  let a : HasRightDual U := { rightDual := E, exact := q }
  let b : HasRightDual U := { rightDual := D, exact := p }
  have hη := @coevaluation_comp_rightAdjointMate C _ _ U U a b (𝟙 U)
  have hε := @rightAdjointMate_comp_evaluation C _ _ U U a b (𝟙 U)
  have h := traceOfPairing_slide (D := D) (E := E) f (𝟙 U)
    (@rightAdjointMate C _ _ U U a b (𝟙 U)) hη hε
  simpa using h

/-- Dinaturality for the chosen right duals. -/
theorem traceOfPairing_dinaturality {X Y U V : C} [HasRightDual U] [HasRightDual V]
    (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U) :
    traceOfPairing (Uᘁ) (f ≫ Y ◁ g) = traceOfPairing (Vᘁ) (X ◁ g ≫ f) :=
  traceOfPairing_slide f g (gᘁ) (coevaluation_comp_rightAdjointMate g)
    (rightAdjointMate_comp_evaluation g)

private theorem cap_slide {U D V : C} (c : U ⊗ D ⟶ 𝟙_ C) :
    (𝟙 (U ⊗ (V ⊗ D)) ⊗≫ U ◁ (β_ V D).hom ⊗≫ c ▷ V ⊗≫ 𝟙 V) =
      (𝟙 (U ⊗ (V ⊗ D)) ⊗≫ (β_ U V).hom ▷ D ⊗≫ V ◁ c ⊗≫ 𝟙 V) := by
  calc
    _ = 𝟙 (U ⊗ (V ⊗ D)) ⊗≫ U ◁ (β_ V D).hom ⊗≫
        (c ▷ V ≫ (β_ (𝟙_ C) V).hom) ⊗≫ 𝟙 V := by
      rw [braiding_tensorUnit_left]
      monoidal
    _ = 𝟙 (U ⊗ (V ⊗ D)) ⊗≫ U ◁ (β_ V D).hom ⊗≫
        ((β_ (U ⊗ D) V).hom ≫ V ◁ c) ⊗≫ 𝟙 V := by
      rw [BraidedCategory.braiding_naturality_left]
    _ = 𝟙 (U ⊗ (V ⊗ D)) ⊗≫ U ◁ ((β_ V D).hom ≫ (β_ D V).hom) ⊗≫
        (β_ U V).hom ▷ D ⊗≫ V ◁ c ⊗≫ 𝟙 V := by
      rw [BraidedCategory.braiding_tensor_left_hom]
      monoidal
    _ = _ := by rw [SymmetricCategory.symmetry]; monoidal

private theorem tensor_cap (U V D E : C) [ExactPairing U D] [ExactPairing V E] :
    (β_ (U ⊗ V) (E ⊗ D)).hom ≫ ε_ (U ⊗ V) (E ⊗ D) =
      (𝟙 ((U ⊗ V) ⊗ (E ⊗ D)) ⊗≫
        (U ◁ ((β_ V E).hom ≫ ε_ V E)) ▷ D ⊗≫
        (β_ U D).hom ≫ ε_ U D) := by
  let c : U ⊗ D ⟶ 𝟙_ C := (β_ U D).hom ≫ ε_ U D
  calc
    _ = 𝟙 ((U ⊗ V) ⊗ (E ⊗ D)) ⊗≫ U ◁ (β_ V E).hom ▷ D ⊗≫
        (β_ U E).hom ▷ (V ⊗ D) ⊗≫
        E ◁ (𝟙 (U ⊗ (V ⊗ D)) ⊗≫ U ◁ (β_ V D).hom ⊗≫
          c ▷ V ⊗≫ 𝟙 V) ⊗≫ ε_ V E := by
      dsimp only [c]
      rw [ExactPairing.tensor_evaluation]
      simp only [BraidedCategory.braiding_tensor_left_hom,
        BraidedCategory.braiding_tensor_right_hom]
      monoidal
    _ = 𝟙 ((U ⊗ V) ⊗ (E ⊗ D)) ⊗≫ U ◁ (β_ V E).hom ▷ D ⊗≫
        (β_ U E).hom ▷ (V ⊗ D) ⊗≫
        E ◁ (𝟙 (U ⊗ (V ⊗ D)) ⊗≫ (β_ U V).hom ▷ D ⊗≫
          V ◁ c ⊗≫ 𝟙 V) ⊗≫ ε_ V E := by rw [cap_slide]
    _ = 𝟙 ((U ⊗ V) ⊗ (E ⊗ D)) ⊗≫ U ◁ (β_ V E).hom ▷ D ⊗≫
        (β_ U (E ⊗ V)).hom ▷ D ⊗≫
        ((E ⊗ V) ◁ c ≫ ε_ V E ▷ (𝟙_ C)) ⊗≫ 𝟙 (𝟙_ C) := by
      rw [BraidedCategory.braiding_tensor_right_hom]
      monoidal
    _ = 𝟙 ((U ⊗ V) ⊗ (E ⊗ D)) ⊗≫ U ◁ (β_ V E).hom ▷ D ⊗≫
        ((β_ U (E ⊗ V)).hom ≫ ε_ V E ▷ U) ▷ D ⊗≫ c := by
      rw [whisker_exchange]
      monoidal
    _ = 𝟙 ((U ⊗ V) ⊗ (E ⊗ D)) ⊗≫ U ◁ (β_ V E).hom ▷ D ⊗≫
        (U ◁ ε_ V E ≫ (β_ U (𝟙_ C)).hom) ▷ D ⊗≫ c := by
      rw [← BraidedCategory.braiding_naturality_right]
    _ = _ := by
      rw [braiding_tensorUnit_right]
      dsimp only [c]
      monoidal

/-- Feedback over a tensor product is successive feedback over its factors. -/
theorem traceOfPairing_tensor {X Y U V D E : C} [ExactPairing U D]
    [ExactPairing V E] (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)) :
    traceOfPairing (E ⊗ D) f =
      traceOfPairing D (traceOfPairing E
        ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv)) := by
  conv_lhs =>
    unfold traceOfPairing
    rw [← whiskerLeft_comp_assoc, tensor_cap, ExactPairing.tensor_coevaluation]
  unfold traceOfPairing
  monoidal

end SymmetricTrace
/-- The canonical symmetric trace induced by duality in a right rigid category. -/
def symmetricTraceOfRigid (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C] [RightRigidCategory C] : SymmetricTrace C where
  trace {X Y U} f := SymmetricTrace.traceOfPairing (Uᘁ) f
  naturality f g h := SymmetricTrace.traceOfPairing_naturality _ f g h
  dinaturality f g := by
    simpa only [id_tensorHom] using SymmetricTrace.traceOfPairing_dinaturality f g
  vanishing_unit f := (SymmetricTrace.traceOfPairing_independent f).trans
    (SymmetricTrace.traceOfPairing_unit f)
  vanishing_tensor {X Y U V} f :=
    (SymmetricTrace.traceOfPairing_independent (E := (Vᘁ) ⊗ (Uᘁ)) f).trans
      (SymmetricTrace.traceOfPairing_tensor f)
  superposing f g := SymmetricTrace.traceOfPairing_superposing _ f g
  yanking X := SymmetricTrace.traceOfPairing_yanking X _

end CategoryTheory
