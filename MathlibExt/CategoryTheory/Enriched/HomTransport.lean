/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.EnrichedHomTransport

section

-- Author: @toskua, Codex


/-!
# Full Hom-isomorphism transport on the original enriched objects

The existing genuine Hom transport constructs the enrichment on exactly the
selected Hom objects and unchanged objects. These bidirectional readbacks and
identity-on-object enriched functors retain both actual inverse Hom maps,
all scalar inputs, and the original monoidal unit and associativity arrows.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedHomTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [original : EnrichedCategory V C]
  (H : C → C → V) (e : ∀ X Y : C, (X ⟶[V] Y) ≅ H X Y)

/-- The transported category has precisely the selected actual Hom objects on unchanged objects. -/
theorem onOriginal_hom (X Y : C) :
    (enrichedCategoryOnOriginalObjects H e).Hom X Y = H X Y := rfl

/-- The whole transported identity uses the same original identity and actual Hom isomorphism. -/
theorem onOriginal_id (X : C) :
    (enrichedCategoryOnOriginalObjects H e).id X = eId V X ≫ (e X X).hom := rfl

/-- The whole transported composition uses both actual inverse Hom maps and the original
composition. -/
theorem onOriginal_comp (X Y Z : C) :
    (enrichedCategoryOnOriginalObjects H e).comp X Y Z =
      ((e X Y).inv ⊗ₘ (e Y Z).inv) ≫ eComp V X Y Z ≫ (e X Z).hom := rfl

/-- The entire original identity is recovered by the same actual inverse Hom isomorphism. -/
theorem onOriginal_id_inv (X : C) :
    (enrichedCategoryOnOriginalObjects H e).id X ≫ (e X X).inv = eId V X := by
  simp only [onOriginal_id, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The complete inverse readback retains both original inverse input maps. -/
theorem onOriginal_comp_inv (X Y Z : C) :
    (enrichedCategoryOnOriginalObjects H e).comp X Y Z ≫ (e X Z).inv =
      ((e X Y).inv ⊗ₘ (e Y Z).inv) ≫ eComp V X Y Z := by
  simp only [onOriginal_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Both original forward Hom maps carry the original whole composition to the new composition. -/
theorem onOriginal_comp_hom (X Y Z : C) :
    ((e X Y).hom ⊗ₘ (e Y Z).hom) ≫ (enrichedCategoryOnOriginalObjects H e).comp X Y Z =
      eComp V X Y Z ≫ (e X Z).hom := by
  rw [onOriginal_comp, ← Category.assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id, Iso.hom_inv_id, id_tensorHom_id, Category.id_comp]

/-- The original composition is recovered on both full inputs and the full output Hom object. -/
theorem onOriginal_comp_recover (X Y Z : C) :
    ((e X Y).hom ⊗ₘ (e Y Z).hom) ≫ (enrichedCategoryOnOriginalObjects H e).comp X Y Z ≫
      (e X Z).inv = eComp V X Y Z := by
  rw [← Category.assoc, onOriginal_comp_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual transported category has the full original left unit with its actual value unitor. -/
theorem onOriginal_id_comp (X Y : C) :
    (λ_ (H X Y)).inv ≫ (enrichedCategoryOnOriginalObjects H e).id X ▷ H X Y ≫
      (enrichedCategoryOnOriginalObjects H e).comp X X Y = 𝟙 (H X Y) :=
  (enrichedCategoryOnOriginalObjects H e).id_comp X Y

/-- The actual transported category has the full original right unit with its actual value
unitor. -/
theorem onOriginal_comp_id (X Y : C) :
    (ρ_ (H X Y)).inv ≫ H X Y ◁ (enrichedCategoryOnOriginalObjects H e).id Y ≫
      (enrichedCategoryOnOriginalObjects H e).comp X Y Y = 𝟙 (H X Y) :=
  (enrichedCategoryOnOriginalObjects H e).comp_id X Y

/-- The actual transported composition associates with the full original monoidal coherence
arrow. -/
theorem onOriginal_assoc (W X Y Z : C) :
    (α_ (H W X) (H X Y) (H Y Z)).inv ≫
      (enrichedCategoryOnOriginalObjects H e).comp W X Y ▷ H Y Z ≫
        (enrichedCategoryOnOriginalObjects H e).comp W Y Z =
      H W X ◁ (enrichedCategoryOnOriginalObjects H e).comp X Y Z ≫
        (enrichedCategoryOnOriginalObjects H e).comp W X Z :=
  (enrichedCategoryOnOriginalObjects H e).assoc W X Y Z

/-- Every pair of arbitrary scalar inputs retains the original whole forward composition word. -/
theorem onOriginal_comp_inputs (X Y Z : C) {U W : V}
    (f : U ⟶ (X ⟶[V] Y)) (g : W ⟶ (Y ⟶[V] Z)) :
    ((f ≫ (e X Y).hom) ⊗ₘ (g ≫ (e Y Z).hom)) ≫
        (enrichedCategoryOnOriginalObjects H e).comp X Y Z =
      (f ⊗ₘ g) ≫ eComp V X Y Z ≫ (e X Z).hom := by
  rw [← tensorHom_comp_tensorHom, Category.assoc, onOriginal_comp_hom]

/-- Every pair of arbitrary selected scalar inputs retains both actual inverse input maps. -/
theorem onOriginal_comp_inputs_inv (X Y Z : C) {U W : V}
    (f : U ⟶ H X Y) (g : W ⟶ H Y Z) :
    ((f ≫ (e X Y).inv) ⊗ₘ (g ≫ (e Y Z).inv)) ≫ eComp V X Y Z =
      (f ⊗ₘ g) ≫ (enrichedCategoryOnOriginalObjects H e).comp X Y Z ≫ (e X Z).inv := by
  rw [← tensorHom_comp_tensorHom, Category.assoc, onOriginal_comp_inv]

/-- The entire forward comparison is natural under every original change of scalar inputs. -/
theorem onOriginal_comp_inputs_naturality (X Y Z : C) {U U' W W' : V}
    (u : U' ⟶ U) (v : W' ⟶ W) (f : U ⟶ (X ⟶[V] Y)) (g : W ⟶ (Y ⟶[V] Z)) :
    (((u ≫ f) ≫ (e X Y).hom) ⊗ₘ ((v ≫ g) ≫ (e Y Z).hom)) ≫
        (enrichedCategoryOnOriginalObjects H e).comp X Y Z =
      (u ⊗ₘ v) ≫ ((f ⊗ₘ g) ≫ eComp V X Y Z ≫ (e X Z).hom) := by
  rw [onOriginal_comp_inputs, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]

/-- The entire inverse comparison is natural under every original change of scalar inputs. -/
theorem onOriginal_comp_inputs_inv_naturality (X Y Z : C) {U U' W W' : V}
    (u : U' ⟶ U) (v : W' ⟶ W) (f : U ⟶ H X Y) (g : W ⟶ H Y Z) :
    (((u ≫ f) ≫ (e X Y).inv) ⊗ₘ ((v ≫ g) ≫ (e Y Z).inv)) ≫ eComp V X Y Z =
      (u ⊗ₘ v) ≫ ((f ⊗ₘ g) ≫ (enrichedCategoryOnOriginalObjects H e).comp X Y Z ≫ (e X Z).inv) := by
  rw [onOriginal_comp_inputs_inv, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]

/-- The forward comparison uses the tagged presentation while retaining every original object. -/
def toTransport : EnrichedFunctor V C (Objects H e) where
  obj X := ⟨X⟩
  map X Y := (e X Y).hom
  map_id X := (onOriginal_id H e X).symm
  map_comp X Y Z := (onOriginal_comp_hom H e X Y Z).symm

/-- The actual inverse comparison keeps every original object and complete inverse Hom map. -/
def fromTransport : EnrichedFunctor V (Objects H e) C where
  obj X := X.asOld
  map X Y := (e X.asOld Y.asOld).inv
  map_id X := identity_inverse H e X
  map_comp X Y Z := composition_inverse H e X Y Z

/-- The forward enriched functor keeps each original object exactly. -/
theorem toTransport_obj (X : C) : ((toTransport H e).obj X).asOld = X := rfl

/-- The forward enriched functor keeps the complete actual chosen Hom isomorphism. -/
theorem toTransport_map (X Y : C) : (toTransport H e).map X Y = (e X Y).hom := rfl

/-- The inverse enriched functor keeps each same original object exactly. -/
theorem fromTransport_obj (X : Objects H e) : (fromTransport H e).obj X = X.asOld := rfl

/-- The inverse enriched functor keeps the complete actual chosen inverse Hom isomorphism. -/
theorem fromTransport_map (X Y : Objects H e) :
    (fromTransport H e).map X Y = (e X.asOld Y.asOld).inv := rfl

/-- The whole forward-then-inverse enriched functor is the original identity enriched functor. -/
theorem toTransport_comp_fromTransport :
    EnrichedFunctor.comp V (toTransport H e) (fromTransport H e) = EnrichedFunctor.id V C := by
  apply EnrichedFunctor.ext V
    (F := EnrichedFunctor.comp V (toTransport H e) (fromTransport H e))
    (G := EnrichedFunctor.id V C) (fun _ ↦ rfl)
  intro X Y
  change ((e X Y).hom ≫ (e X Y).inv) ≫ 𝟙 (X ⟶[V] Y) = 𝟙 (X ⟶[V] Y)
  rw [Category.comp_id, Iso.hom_inv_id]

/-- The whole inverse-then-forward enriched functor is the actual transported identity enriched
functor. -/
theorem fromTransport_comp_toTransport :
    EnrichedFunctor.comp V (fromTransport H e) (toTransport H e) =
      EnrichedFunctor.id V (Objects H e) := by
  apply EnrichedFunctor.ext V
    (F := EnrichedFunctor.comp V (fromTransport H e) (toTransport H e))
    (G := EnrichedFunctor.id V (Objects H e)) (fun _ ↦ rfl)
  intro X Y
  change ((e X.asOld Y.asOld).inv ≫ (e X.asOld Y.asOld).hom) ≫
    𝟙 (H X.asOld Y.asOld) = 𝟙 (H X.asOld Y.asOld)
  rw [Category.comp_id, Iso.inv_hom_id]

end CategoryTheory.EnrichedHomTransport

end
end
end
