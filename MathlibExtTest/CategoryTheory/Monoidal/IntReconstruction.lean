/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntReconstruction
import MathlibExt.CategoryTheory.Monoidal.RelCat
import Mathlib.Algebra.Category.FGModuleCat.Basic

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable (T : SymmetricTrace C)
example {X Y : IntConstruction T} (f : X ⟶ Y) :
    IntConstruction.reconstruct T (IntConstruction.hom T f) = f :=
  IntConstruction.reconstruct_hom T f

open IntConstruction

-- Both directions work for arbitrary objects and a supplied, non-canonical trace.
example {X Y : IntConstruction T}
    (f : X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative) :
    hom T (reconstruct T (X := X) (Y := Y) f) = f := by
  simp only [hom_reconstruct]
example {X Y : IntConstruction T}
    (f : X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative) :
    reconstruct T (X := X) (Y := Y) f = ofHom T f := reconstruct_hom T (ofHom T f)
example (X : IntConstruction T) : reconstruct T (hom T (𝟙 X)) = 𝟙 X := by
  simp only [reconstruct_hom]
example {X Y Z : IntConstruction T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    reconstruct T (hom T (f ≫ g)) = reconstruct T (hom T f) ≫ reconstruct T (hom T g) := by
  simp only [reconstruct_hom]
example {X₁ X₂ Y₁ Y₂ : IntConstruction T} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    reconstruct T (hom T (f ⊗ₘ g)) = f ⊗ₘ g := by
  simp only [reconstruct_hom]
example (X Y : IntConstruction T) :
    reconstruct T (hom T (β_ X Y).hom) = (β_ X Y).hom := by
  simp only [reconstruct_hom]
example {A B : C} (f : A ⟶ B) :
    reconstruct T (hom T ((embedding T).map f)) = (embedding T).map f := by
  simp only [reconstruct_hom]
example (X : IntConstruction T) :
    reconstruct T (hom T (λ_ X).hom) = (λ_ X).hom := by
  simp only [reconstruct_hom]
example (X : IntConstruction T) :
    reconstruct T (hom T (ρ_ X).inv) = (ρ_ X).inv := by
  simp only [reconstruct_hom]

-- The exported right bend uses the named elementary pairing, not the global transported one.
example {X Y : IntConstruction T} (A : C) (f : X ⊗ (embedding T).obj A ⟶ Y) :
    rightMate T A f = (ρ_ X).inv ≫ X ◁ (positivePairing T A).coevaluation' ≫
      (α_ X (⟨A, 𝟙_ C⟩ : IntConstruction T) (⟨𝟙_ C, A⟩ : IntConstruction T)).inv ≫
        f ▷ (⟨𝟙_ C, A⟩ : IntConstruction T) := rfl
example (A : C) :
    reconstruct T (hom T (positivePairing T A).coevaluation') =
      (positivePairing T A).coevaluation' := by
  simp only [reconstruct_hom]
example (A : C) :
    reconstruct T (hom T (positivePairing T A).evaluation') =
      (positivePairing T A).evaluation' := by
  simp only [reconstruct_hom]

noncomputable section
private abbrev relationalTrace := RelCat.symmetricTrace.{0}

-- Relation membership survives reconstruction with all four components present.
example (P U B V : RelCat.{0}) (r : P ⊗ V ⟶ B ⊗ U)
    (p : P) (u : U) (b : B) (v : V) :
    (((p,v),(b,u)) ∈ (hom relationalTrace (reconstruct relationalTrace (X := ⟨P,U⟩) (Y := ⟨B,V⟩) r)).rel) ↔
      ((p,v),(b,u)) ∈ r.rel := by rw [hom_reconstruct]
example (P U B V : RelCat.{0}) :
    (hom relationalTrace (reconstruct relationalTrace (X := ⟨P,U⟩) (Y := ⟨B,V⟩)
      (RelCat.Hom.ofRel ∅ : P ⊗ V ⟶ B ⊗ U))).rel = ∅ := by rw [hom_reconstruct]
example (P U B V : RelCat.{0}) :
    (hom relationalTrace (reconstruct relationalTrace (X := ⟨P,U⟩) (Y := ⟨B,V⟩)
      (RelCat.Hom.ofRel Set.univ : P ⊗ V ⟶ B ⊗ U))).rel = Set.univ := by
  rw [hom_reconstruct]

private abbrev linearTrace := symmetricTraceOfRigid (FGModuleCat ℚ)
-- Zero and nonzero scalar maps test the linear model, with two non-unit components.
example (P U B V : FGModuleCat ℚ) :
    hom linearTrace (reconstruct linearTrace (X := ⟨P,U⟩) (Y := ⟨B,V⟩) (0 : P ⊗ V ⟶ B ⊗ U)) = 0 := by
  simp only [hom_reconstruct]
example (P U : FGModuleCat ℚ) :
    hom linearTrace (reconstruct linearTrace (X := ⟨P,U⟩) (Y := ⟨P,U⟩) ((2 : ℚ) • 𝟙 (P ⊗ U))) =
      (2 : ℚ) • 𝟙 (P ⊗ U) := by
  simp only [hom_reconstruct]
