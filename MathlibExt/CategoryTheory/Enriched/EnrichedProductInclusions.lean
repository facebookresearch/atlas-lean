/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic

/-!
# Enriched product inclusions with one object fixed

The actual enriched identity supplies the fixed factor. These shared implementations retain
all complete Hom maps and the original braided monoidal universe scope, for plain enriched
source types. They are the canonical inclusions used by Day convolution and enriched coends.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe uV vV uA uB

namespace CategoryTheory.EnrichedFunctor

open MonoidalCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
variable {A : Type uA} [EnrichedCategory V A]
variable {B : Type uB} [EnrichedCategory V B]

attribute [local instance] Enriched.prodCategory

omit [BraidedCategory V] in
private theorem identity_comp {D : Type*} [EnrichedCategory V D] (e : D) :
    (eId V e ⊗ₘ eId V e) ≫ eComp V e e e = (λ_ (𝟙_ V)).hom ≫ eId V e := by
  rw [← cancel_epi (λ_ (𝟙_ V)).inv]
  simp only [Iso.inv_hom_id_assoc]
  rw [leftUnitor_inv_comp_tensorHom_assoc, e_id_comp, Category.comp_id]

omit [BraidedCategory V] in
private theorem tensor_unitor {X Y Z : V} (f : X ⟶ Y) (g : 𝟙_ V ⟶ Z) :
    f ⊗ₘ g = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv ≫ Y ◁ g := by
  rw [← cancel_epi (ρ_ X).inv]
  simp only [Iso.inv_hom_id_assoc]
  exact rightUnitor_inv_comp_tensorHom f g

omit [BraidedCategory V] in
private theorem tensor_unitor_left {X Y Z : V} (f : 𝟙_ V ⟶ Y) (g : X ⟶ Z) :
    f ⊗ₘ g = (λ_ X).hom ≫ g ≫ (λ_ Z).inv ≫ f ▷ Z := by
  rw [← cancel_epi (λ_ X).inv]
  simp only [Iso.inv_hom_id_assoc]
  exact leftUnitor_inv_comp_tensorHom f g

/-- The enriched inclusion `i ↦ (i, e)`, whose Hom map inserts the enriched identity of
  the fixed right object. -/
def prodLeftInclusion (e : B) : EnrichedFunctor V A (A × B) where
  obj i := (i, e)
  map i j := (ρ_ (i ⟶[V] j)).inv ≫ (𝟙 (i ⟶[V] j) ⊗ₘ eId V e)
  map_id i := by
    change eId V i ≫ (ρ_ (i ⟶[V] i)).inv ≫
        (𝟙 (i ⟶[V] i) ⊗ₘ eId V e) =
      (λ_ (𝟙_ V)).inv ≫ (eId V i ⊗ₘ eId V e)
    rw [rightUnitor_inv_naturality_assoc, unitors_inv_equal]
    slice_lhs 2 3 =>
      rw [← tensorHom_id, tensorHom_comp_tensorHom]
      simp
  map_comp i j k := by
    change eComp V i j k ≫ (ρ_ (i ⟶[V] k)).inv ≫
        (𝟙 (i ⟶[V] k) ⊗ₘ eId V e) =
      (((ρ_ (i ⟶[V] j)).inv ≫ (𝟙 (i ⟶[V] j) ⊗ₘ eId V e)) ⊗ₘ
        ((ρ_ (j ⟶[V] k)).inv ≫ (𝟙 (j ⟶[V] k) ⊗ₘ eId V e))) ≫
        tensorμ (i ⟶[V] j) (e ⟶[V] e) (j ⟶[V] k) (e ⟶[V] e) ≫
        (eComp V i j k ⊗ₘ eComp V e e e)
    rw [← cancel_epi (ρ_ ((i ⟶[V] j) ⊗ (j ⟶[V] k))).hom]
    nth_rewrite 2 [tensor_right_unitality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [tensorμ_natural_assoc, tensorHom_comp_tensorHom]
    simp only [id_tensorHom_id, Category.id_comp]
    rw [identity_comp]
    nth_rewrite 2 [← Category.id_comp (eComp V i j k)]
    rw [← tensorHom_comp_tensorHom]
    simp only [id_tensorHom]
    rw [tensor_unitor, ← rightUnitor_monoidal_assoc, ← tensor_right_unitality_assoc]

/-- Insert a fixed first input and its actual enriched identity on the full varying Hom. -/
def prodRightInclusion (e : A) : EnrichedFunctor V B (A × B) where
  obj i := (e, i)
  map i j := (λ_ (i ⟶[V] j)).inv ≫ (eId V e ⊗ₘ 𝟙 (i ⟶[V] j))
  map_id i := by
    change eId V i ≫ (λ_ (i ⟶[V] i)).inv ≫
        (eId V e ⊗ₘ 𝟙 (i ⟶[V] i)) =
      (λ_ (𝟙_ V)).inv ≫ (eId V e ⊗ₘ eId V i)
    rw [leftUnitor_inv_naturality_assoc]
    slice_lhs 2 3 =>
      rw [← id_tensorHom, tensorHom_comp_tensorHom]
      simp
  map_comp i j k := by
    change eComp V i j k ≫ (λ_ (i ⟶[V] k)).inv ≫
        (eId V e ⊗ₘ 𝟙 (i ⟶[V] k)) =
      (((λ_ (i ⟶[V] j)).inv ≫ (eId V e ⊗ₘ 𝟙 (i ⟶[V] j))) ⊗ₘ
        ((λ_ (j ⟶[V] k)).inv ≫ (eId V e ⊗ₘ 𝟙 (j ⟶[V] k)))) ≫
        tensorμ (e ⟶[V] e) (i ⟶[V] j) (e ⟶[V] e) (j ⟶[V] k) ≫
        (eComp V e e e ⊗ₘ eComp V i j k)
    rw [← cancel_epi (λ_ ((i ⟶[V] j) ⊗ (j ⟶[V] k))).hom]
    nth_rewrite 2 [tensor_left_unitality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [tensorμ_natural_assoc, tensorHom_comp_tensorHom]
    simp only [id_tensorHom_id, Category.id_comp]
    rw [identity_comp]
    nth_rewrite 2 [← Category.id_comp (eComp V i j k)]
    rw [← tensorHom_comp_tensorHom]
    simp only [tensorHom_id]
    rw [tensor_unitor_left, ← leftUnitor_monoidal_assoc, ← tensor_left_unitality_assoc]

/-- The left-variable inclusion has its literal fixed-right object. -/
@[simp]
theorem prodLeftInclusion_obj (b : B) (a : A) :
    (prodLeftInclusion (V := V) (A := A) b).obj a = (a, b) := rfl

/-- The right-variable inclusion has its literal fixed-left object. -/
@[simp]
theorem prodRightInclusion_obj (a : A) (b : B) :
    (prodRightInclusion (V := V) (B := B) a).obj b = (a, b) := rfl

/-- The left-variable inclusion keeps the entire original enriched Hom map. -/
theorem prodLeftInclusion_map (b : B) (a a' : A) :
    (prodLeftInclusion (V := V) (A := A) b).map a a' =
      (ρ_ (a ⟶[V] a')).inv ≫ (𝟙 (a ⟶[V] a') ⊗ₘ eId V b) := rfl

/-- The right-variable inclusion keeps the entire original enriched Hom map. -/
theorem prodRightInclusion_map (a : A) (b b' : B) :
    (prodRightInclusion (V := V) (B := B) a).map b b' =
      (λ_ (b ⟶[V] b')).inv ≫ (eId V a ⊗ₘ 𝟙 (b ⟶[V] b')) := rfl


end CategoryTheory.EnrichedFunctor

namespace CategoryTheory.EnrichedFunctor

section Cartesian

variable {V : Type uV} [Category.{vV} V] [CartesianMonoidalCategory V]
variable {A : Type uA} [EnrichedCategory V A]
variable {B : Type uB} [EnrichedCategory V B]

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory Enriched.prodCategory

/-- In a Cartesian base, the canonical fixed-right inclusion has the full paired Hom map. -/
theorem prodLeftInclusion_map_cartesian (b : B) (a a' : A) :
    (prodLeftInclusion (V := V) (A := A) b).map a a' =
      CartesianMonoidalCategory.lift (𝟙 (a ⟶[V] a'))
        (CartesianMonoidalCategory.toUnit (a ⟶[V] a') ≫ eId V b) := by
  rw [prodLeftInclusion_map]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, CartesianMonoidalCategory.tensorHom_fst, ← Category.assoc,
      CartesianMonoidalCategory.rightUnitor_inv_fst, Category.id_comp,
      CartesianMonoidalCategory.lift_fst]
  · rw [Category.assoc, CartesianMonoidalCategory.tensorHom_snd, ← Category.assoc,
      CartesianMonoidalCategory.rightUnitor_inv_snd, CartesianMonoidalCategory.lift_snd]

/-- The canonical fixed-left inclusion has the original constant/identity Cartesian Hom map. -/
theorem prodRightInclusion_map_cartesian (a : A) (b b' : B) :
    (prodRightInclusion (V := V) (B := B) a).map b b' =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.toUnit (b ⟶[V] b') ≫ eId V a) (𝟙 (b ⟶[V] b')) := by
  rw [prodRightInclusion_map]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, CartesianMonoidalCategory.tensorHom_fst, ← Category.assoc,
      CartesianMonoidalCategory.leftUnitor_inv_fst, CartesianMonoidalCategory.lift_fst]
  · rw [Category.assoc, CartesianMonoidalCategory.tensorHom_snd, ← Category.assoc,
      CartesianMonoidalCategory.leftUnitor_inv_snd, Category.id_comp,
      CartesianMonoidalCategory.lift_snd]

end Cartesian

end CategoryTheory.EnrichedFunctor
