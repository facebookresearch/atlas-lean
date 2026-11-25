/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Full enriched Hom transport along actual isomorphisms

Objects are tagged only by the selected Hom objects and their actual proved
isomorphisms. Identity, composition, both units and full associativity are
derived from the original enriched category. A target enrichment or law
dictionary is not an input.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uV vV uC

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedHomTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C]

/-- Tag the original objects by their proved complete Hom presentation. -/
structure Objects (Q : C → C → V) (e : ∀ X Y : C, (X ⟶[V] Y) ≅ Q X Y) where
  /-- The original object. -/
  asOld : C

variable (Q : C → C → V) (e : ∀ X Y : C, (X ⟶[V] Y) ≅ Q X Y)

/-- Original identity followed by the actual complete Hom isomorphism. -/
def identity (X : Objects Q e) : 𝟙_ V ⟶ Q X.asOld X.asOld :=
  eId V X.asOld ≫ (e X.asOld X.asOld).hom

/-- Both complete inverse Hom maps followed by the original composition. -/
def composition (X Y Z : Objects Q e) :
    Q X.asOld Y.asOld ⊗ Q Y.asOld Z.asOld ⟶ Q X.asOld Z.asOld :=
  ((e X.asOld Y.asOld).inv ⊗ₘ (e Y.asOld Z.asOld).inv) ≫
    eComp V X.asOld Y.asOld Z.asOld ≫ (e X.asOld Z.asOld).hom

/-- The original enriched identity is recovered as a full morphism. -/
theorem identity_inverse (X : Objects Q e) :
    identity Q e X ≫ (e X.asOld X.asOld).inv = eId V X.asOld := by
  simp only [identity, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original enriched composition is recovered on both complete Hom objects. -/
theorem composition_inverse (X Y Z : Objects Q e) :
    composition Q e X Y Z ≫ (e X.asOld Z.asOld).inv =
      ((e X.asOld Y.asOld).inv ⊗ₘ (e Y.asOld Z.asOld).inv) ≫
        eComp V X.asOld Y.asOld Z.asOld := by
  simp only [composition, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The full left unit is derived from the original unit and inverse Hom maps. -/
theorem identity_comp (X Y : Objects Q e) :
    (λ_ (Q X.asOld Y.asOld)).inv ≫ identity Q e X ▷ (Q X.asOld Y.asOld) ≫
      composition Q e X X Y = 𝟙 (Q X.asOld Y.asOld) := by
  let H : V := X.asOld ⟶[V] Y.asOld
  let P : V := Q X.asOld Y.asOld
  let p : P ⟶ H := (e X.asOld Y.asOld).inv
  let i : 𝟙_ V ⟶ (X.asOld ⟶[V] X.asOld) := eId V X.asOld
  have hcollect : (λ_ P).inv ≫ (i ⊗ₘ p) =
      p ≫ (λ_ H).inv ≫ (i ⊗ₘ 𝟙 H) := by
    rw [leftUnitor_inv_naturality_assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  apply (cancel_mono (e X.asOld Y.asOld).inv).1
  simp only [Category.assoc, composition_inverse, Category.id_comp]
  change (λ_ P).inv ≫ identity Q e X ▷ P ≫
      ((e X.asOld X.asOld).inv ⊗ₘ p) ≫ eComp V X.asOld X.asOld Y.asOld = p
  rw [whiskerRight_comp_tensorHom_assoc, identity_inverse]
  calc
    _ = p ≫ (λ_ H).inv ≫ (i ⊗ₘ 𝟙 H) ≫ eComp V X.asOld X.asOld Y.asOld := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ eComp V X.asOld X.asOld Y.asOld) hcollect
    _ = p := by rw [tensorHom_id, e_id_comp, Category.comp_id]

/-- The full right unit is derived from the original unit and inverse Hom maps. -/
theorem comp_identity (X Y : Objects Q e) :
    (ρ_ (Q X.asOld Y.asOld)).inv ≫ (Q X.asOld Y.asOld) ◁ identity Q e Y ≫
      composition Q e X Y Y = 𝟙 (Q X.asOld Y.asOld) := by
  let H : V := X.asOld ⟶[V] Y.asOld
  let P : V := Q X.asOld Y.asOld
  let p : P ⟶ H := (e X.asOld Y.asOld).inv
  let i : 𝟙_ V ⟶ (Y.asOld ⟶[V] Y.asOld) := eId V Y.asOld
  have hcollect : (ρ_ P).inv ≫ (p ⊗ₘ i) =
      p ≫ (ρ_ H).inv ≫ (𝟙 H ⊗ₘ i) := by
    rw [rightUnitor_inv_naturality_assoc, ← tensorHom_id,
      tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  apply (cancel_mono (e X.asOld Y.asOld).inv).1
  simp only [Category.assoc, composition_inverse, Category.id_comp]
  change (ρ_ P).inv ≫ P ◁ identity Q e Y ≫
      (p ⊗ₘ (e Y.asOld Y.asOld).inv) ≫ eComp V X.asOld Y.asOld Y.asOld = p
  rw [whiskerLeft_comp_tensorHom_assoc, identity_inverse]
  calc
    _ = p ≫ (ρ_ H).inv ≫ (𝟙 H ⊗ₘ i) ≫ eComp V X.asOld Y.asOld Y.asOld := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ eComp V X.asOld Y.asOld Y.asOld) hcollect
    _ = p := by rw [id_tensorHom, e_comp_id, Category.comp_id]

/-- Full three-Hom associativity follows from the original associativity square. -/
theorem assoc (W X Y Z : Objects Q e) :
    (α_ (Q W.asOld X.asOld) (Q X.asOld Y.asOld) (Q Y.asOld Z.asOld)).inv ≫
        composition Q e W X Y ▷ (Q Y.asOld Z.asOld) ≫ composition Q e W Y Z =
      (Q W.asOld X.asOld) ◁ composition Q e X Y Z ≫ composition Q e W X Z := by
  let A : V := W.asOld ⟶[V] X.asOld
  let B : V := X.asOld ⟶[V] Y.asOld
  let C' : V := Y.asOld ⟶[V] Z.asOld
  let P : V := Q W.asOld X.asOld
  let Q' : V := Q X.asOld Y.asOld
  let R : V := Q Y.asOld Z.asOld
  let f : P ⟶ A := (e W.asOld X.asOld).inv
  let g : Q' ⟶ B := (e X.asOld Y.asOld).inv
  let h : R ⟶ C' := (e Y.asOld Z.asOld).inv
  let a : A ⊗ B ⟶ (W.asOld ⟶[V] Y.asOld) := eComp V W.asOld X.asOld Y.asOld
  let b : B ⊗ C' ⟶ (X.asOld ⟶[V] Z.asOld) := eComp V X.asOld Y.asOld Z.asOld
  let c : (W.asOld ⟶[V] Y.asOld) ⊗ C' ⟶ (W.asOld ⟶[V] Z.asOld) :=
    eComp V W.asOld Y.asOld Z.asOld
  let d : A ⊗ (X.asOld ⟶[V] Z.asOld) ⟶ (W.asOld ⟶[V] Z.asOld) :=
    eComp V W.asOld X.asOld Z.asOld
  have hl : (((f ⊗ₘ g) ≫ a) ⊗ₘ h) =
      ((f ⊗ₘ g) ⊗ₘ h) ≫ (a ⊗ₘ 𝟙 C') := by
    simpa only [Category.comp_id] using
      (tensorHom_comp_tensorHom (f ⊗ₘ g) h a (𝟙 C')).symm
  have hr : (f ⊗ₘ ((g ⊗ₘ h) ≫ b)) =
      (f ⊗ₘ (g ⊗ₘ h)) ≫ (𝟙 A ⊗ₘ b) := by
    simpa only [Category.comp_id] using
      (tensorHom_comp_tensorHom f (g ⊗ₘ h) (𝟙 A) b).symm
  have hn : (α_ P Q' R).inv ≫ ((f ⊗ₘ g) ⊗ₘ h) =
      (f ⊗ₘ (g ⊗ₘ h)) ≫ (α_ A B C').inv :=
    (associator_inv_naturality f g h).symm
  have ho : (α_ A B C').inv ≫ (a ⊗ₘ 𝟙 C') ≫ c = (𝟙 A ⊗ₘ b) ≫ d := by
    simpa only [tensorHom_id, id_tensorHom] using e_assoc V W.asOld X.asOld Y.asOld Z.asOld
  apply (cancel_mono (e W.asOld Z.asOld).inv).1
  simp only [Category.assoc, composition_inverse]
  rw [whiskerRight_comp_tensorHom_assoc, composition_inverse,
    whiskerLeft_comp_tensorHom_assoc, composition_inverse]
  change (α_ P Q' R).inv ≫ (((f ⊗ₘ g) ≫ a) ⊗ₘ h) ≫ c =
    (f ⊗ₘ ((g ⊗ₘ h) ≫ b)) ≫ d
  rw [hl, hr]
  calc
    _ = (f ⊗ₘ (g ⊗ₘ h)) ≫ (α_ A B C').inv ≫ (a ⊗ₘ 𝟙 C') ≫ c := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ (a ⊗ₘ 𝟙 C') ≫ c) hn
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun q => (f ⊗ₘ (g ⊗ₘ h)) ≫ q) ho

/-- The complete derived enrichment, using exactly the selected actual Hom objects. -/
instance enrichedCategory : EnrichedCategory V (Objects Q e) where
  Hom X Y := Q X.asOld Y.asOld
  id X := identity Q e X
  comp X Y Z := composition Q e X Y Z
  id_comp X Y := identity_comp Q e X Y
  comp_id X Y := comp_identity Q e X Y
  assoc W X Y Z := assoc Q e W X Y Z

end CategoryTheory.EnrichedHomTransport

namespace CategoryTheory.EnrichedHomTransport

variable {W : Type uV} [Category.{vV} W] [MonoidalCategory W]
  {A : Type uC} [EnrichedCategory W A]
  (Q : A → A → W) (e : ∀ X Y : A, (X ⟶[W] Y) ≅ Q X Y)

/-- The already proved complete Hom transport laws on the original unchanged objects. -/
@[instance_reducible]
def enrichedCategoryOnOriginalObjects : EnrichedCategory W A where
  Hom := Q
  id X := identity Q e ⟨X⟩
  comp X Y Z := composition Q e ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  id_comp X Y := identity_comp Q e ⟨X⟩ ⟨Y⟩
  comp_id X Y := comp_identity Q e ⟨X⟩ ⟨Y⟩
  assoc W X Y Z := assoc Q e ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩

end CategoryTheory.EnrichedHomTransport
