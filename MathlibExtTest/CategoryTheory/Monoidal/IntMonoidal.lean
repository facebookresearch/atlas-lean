/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntMonoidal
import Mathlib.Algebra.Category.FGModuleCat.Basic

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable (T : SymmetricTrace C)

-- No rigidity hypothesis: any supplied symmetric trace suffices.
example : MonoidalCategory (IntConstruction T) := inferInstance
example : SymmetricCategory (IntConstruction T) := inferInstance
example : (IntConstruction.embedding T).Monoidal := inferInstance
example : (IntConstruction.embedding T).Braided := inferInstance
example : (IntConstruction.embedding T).Full := inferInstance
example : (IntConstruction.embedding T).Faithful := inferInstance

example (X Y : IntConstruction T) : (X ⊗ Y).positive = X.positive ⊗ Y.positive := by simp
example (X Y : IntConstruction T) : (X ⊗ Y).negative = Y.negative ⊗ X.negative := by simp

-- Exercise tensor composition on arbitrary crossed morphisms, not just separated pairs.
example {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : IntConstruction T}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : Y₁ ⟶ Z₁) (k : Y₂ ⟶ Z₂) :
    (f ⊗ₘ g) ≫ (h ⊗ₘ k) = (f ≫ h) ⊗ₘ (g ≫ k) := by simp

example {X₁ X₂ Y₁ Y₂ : IntConstruction T} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ (β_ Y₁ Y₂).hom = (β_ X₁ X₂).hom ≫ (g ⊗ₘ f) := by simp

example (X Y : IntConstruction T) : (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _ := by simp

-- The structural maps fix the direction of the contravariant negative component.
example (X Y Z : IntConstruction T) :
    IntConstruction.hom T (α_ X Y Z).hom =
      (α_ X.positive Y.positive Z.positive).hom ⊗ₘ
        (α_ Z.negative Y.negative X.negative).hom := rfl

example (X : IntConstruction T) : IntConstruction.hom T (λ_ X).hom =
    (λ_ X.positive).hom ⊗ₘ (ρ_ X.negative).inv := rfl

example (X : IntConstruction T) : IntConstruction.hom T (ρ_ X).hom =
    (ρ_ X.positive).hom ⊗ₘ (λ_ X.negative).inv := rfl

example (X Y : IntConstruction T) : IntConstruction.hom T (β_ X Y).hom =
    (β_ X.positive Y.positive).hom ⊗ₘ (β_ X.negative Y.negative).hom := rfl

-- The negative tensor of embedded objects is I ⊗ I, requiring a comparison isomorphism.
example (X Y : C) :
    IntConstruction.hom T (Functor.LaxMonoidal.μ (IntConstruction.embedding T) X Y) =
      𝟙 (X ⊗ Y) ⊗ₘ (λ_ (𝟙_ C)).inv :=
  IntConstruction.hom_embedding_μ T X Y

-- The explicit rewrite also supports downstream normalization of the crossed hom type.
example (X Y : C) :
    IntConstruction.hom T (Functor.LaxMonoidal.μ (IntConstruction.embedding T) X Y) =
      𝟙 (X ⊗ Y) ⊗ₘ (λ_ (𝟙_ C)).inv := by
  simp only [IntConstruction.hom_embedding_μ]
  rfl

example (X Y : C) :
    IsIso (Functor.LaxMonoidal.μ (IntConstruction.embedding T) X Y) := inferInstance

example (X Y : C) :
    Functor.LaxMonoidal.μ (IntConstruction.embedding T) X Y ≫
      (IntConstruction.embedding T).map (β_ X Y).hom =
    (β_ ((IntConstruction.embedding T).obj X) ((IntConstruction.embedding T).obj Y)).hom ≫
      Functor.LaxMonoidal.μ (IntConstruction.embedding T) Y X :=
  Functor.LaxBraided.braided X Y

-- Separate maps compose contravariantly in the negative slot.
example {X Y Z : IntConstruction T}
    (a : X.positive ⟶ Y.positive) (b : Y.negative ⟶ X.negative)
    (c : Y.positive ⟶ Z.positive) (d : Z.negative ⟶ Y.negative) :
    IntConstruction.mapPair T a b ≫ IntConstruction.mapPair T c d =
      IntConstruction.mapPair T (a ≫ c) (d ≫ b) := by simp

noncomputable section

private abbrev linearTrace := symmetricTraceOfRigid (FGModuleCat ℚ)

-- Tensoring a zero crossed map is zero even with nontrivial negative objects.
example (A B U V A' B' U' V' : FGModuleCat ℚ) (g : A' ⊗ V' ⟶ B' ⊗ U') :
    IntConstruction.hom linearTrace
      (IntConstruction.ofHom linearTrace (X := ⟨A, U⟩) (Y := ⟨B, V⟩) 0 ⊗ₘ
        IntConstruction.ofHom linearTrace (X := ⟨A', U'⟩) (Y := ⟨B', V'⟩) g) = 0 := by
  change IntConstruction.hom linearTrace (IntConstruction.tensorMap linearTrace _ _) = 0
  simp [IntConstruction.tensorMap]

-- The shuffle sends (a ⊗ b) ⊗ (v ⊗ u) to (a ⊗ u) ⊗ (b ⊗ v).
example (A B U V : FGModuleCat ℚ) (a : A) (b : B) (u : U) (v : V) :
    (IntConstruction.tensorShuffle A B U V).hom.hom.hom
      ((a ⊗ₜ[ℚ] b) ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] u)) =
        (a ⊗ₜ[ℚ] u) ⊗ₜ[ℚ] (b ⊗ₜ[ℚ] v) := by
  rfl

-- A mixed tensor of separated maps scales by 2 * (-3), not by a feedback dimension.
example (A B U V : FGModuleCat ℚ) (a : A) (b : B) (u : U) (v : V) :
    (IntConstruction.hom linearTrace
      (IntConstruction.mapPair linearTrace (X := ⟨A, U⟩) (Y := ⟨A, U⟩)
        ((2 : ℚ) • 𝟙 A) (𝟙 U) ⊗ₘ
       IntConstruction.mapPair linearTrace (X := ⟨B, V⟩) (Y := ⟨B, V⟩)
        ((-3 : ℚ) • 𝟙 B) (𝟙 V))).hom.hom
      ((a ⊗ₜ[ℚ] b) ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] u)) =
        (-6 : ℚ) • ((a ⊗ₜ[ℚ] b) ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] u)) := by
  change (IntConstruction.hom linearTrace
    (IntConstruction.tensorMap linearTrace _ _)).hom.hom _ = _
  rw [IntConstruction.tensorMap_mapPair, IntConstruction.hom_mapPair]
  change (((2 : ℚ) • a) ⊗ₜ[ℚ] ((-3 : ℚ) • b)) ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] u) = _
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  norm_num

#print axioms IntConstruction.monoidalCategory
#print axioms IntConstruction.symmetricCategory
#print axioms IntConstruction.embeddingBraided
