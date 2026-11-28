/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntCompact
import Mathlib.Algebra.Category.FGModuleCat.Basic

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable (T : SymmetricTrace C)

-- The source needs a trace, not pre-existing duals.
example : RigidCategory (IntConstruction T) := inferInstance
example : T.Preserves (symmetricTraceOfRigid (IntConstruction T))
    (IntConstruction.embedding T) := IntConstruction.embedding_preserves_trace T

open IntConstruction

example : RightRigidCategory (IntConstruction T) := inferInstance
example : LeftRigidCategory (IntConstruction T) := inferInstance
example (X : IntConstruction T) : HasRightDual X := inferInstance
example (X : IntConstruction T) : HasLeftDual X := inferInstance

-- Both components may be nontrivial; the source need not be rigid.
example (A B : C) : dual T ⟨A, B⟩ = ⟨B, A⟩ := rfl
example (X : IntConstruction T) : dual T (dual T X) = X := by simp
example (X : IntConstruction T) : Xᘁ = dual T X := by simp
example (X : IntConstruction T) : (ᘁX : IntConstruction T) = dual T X := by simp
example (X Y : IntConstruction T) : dual T (X ⊗ Y) = dual T Y ⊗ dual T X := rfl
example : dual T (𝟙_ (IntConstruction T)) = 𝟙_ (IntConstruction T) := rfl

-- The standard duality API exposes both snakes for the selected pairing.
example (X : IntConstruction T) :
    Xᘁ ◁ η_ X Xᘁ ≫ (α_ _ _ _).inv ≫ ε_ X Xᘁ ▷ Xᘁ =
      (ρ_ Xᘁ).hom ≫ (λ_ Xᘁ).inv := ExactPairing.coevaluation_evaluation X Xᘁ
example (X : IntConstruction T) :
    η_ X Xᘁ ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε_ X Xᘁ =
      (λ_ X).hom ≫ (ρ_ X).inv := ExactPairing.evaluation_coevaluation X Xᘁ

-- Named pairings do not replace Mathlib's unit or reversed tensor pairings.
example : ExactPairing (𝟙_ (IntConstruction T)) (𝟙_ (IntConstruction T)) := inferInstance
example (X Y : IntConstruction T) : ExactPairing (X ⊗ Y) (Yᘁ ⊗ Xᘁ) := inferInstance
example (X Y : IntConstruction T) :
    ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) =
      𝟙 _ ⊗≫ (Yᘁ : IntConstruction T) ◁ (ε_ X Xᘁ ▷ Y) ⊗≫ ε_ Y Yᘁ := ExactPairing.tensor_evaluation

example (X : IntConstruction T) :
    X ≅ (⟨X.positive, 𝟙_ C⟩ : IntConstruction T) ⊗ ⟨𝟙_ C, X.negative⟩ :=
  decomposition T X

-- Inspect the explicit elementary pairing, independently of the transported one.
example (A : C) :
    hom T (positivePairing T A).coevaluation' =
      (λ_ (A ⊗ 𝟙_ C)).hom ≫ (ρ_ (A ⊗ 𝟙_ C)).inv := rfl
example (A : C) :
    hom T (positivePairing T A).evaluation' =
      (ρ_ (𝟙_ C ⊗ A)).hom ≫ (λ_ (𝟙_ C ⊗ A)).inv := rfl

-- Arbitrary feedback, including the strong monoidal comparison maps.
example {X Y U : C} (f : X ⊗ U ⟶ Y ⊗ U) :
    (embedding T).map (T.trace f) =
      (symmetricTraceOfRigid (IntConstruction T)).trace
        (Functor.LaxMonoidal.μ (embedding T) X U ≫ (embedding T).map f ≫
          Functor.OplaxMonoidal.δ (embedding T) Y U) := embedding_preserves_trace T f

-- The chosen source trace can be recovered from the target trace via fullness.
example {X Y U : C} (f : X ⊗ U ⟶ Y ⊗ U) :
    (embedding T).preimage ((symmetricTraceOfRigid (IntConstruction T)).trace
      (Functor.LaxMonoidal.μ (embedding T) X U ≫ (embedding T).map f ≫
        Functor.OplaxMonoidal.δ (embedding T) Y U)) = T.trace f := by
  rw [← embedding_preserves_trace T f]
  simp

-- Feedback over the tensor unit recovers an arbitrary embedded morphism.
example {X Y : C} (f : X ⟶ Y) :
    (symmetricTraceOfRigid (IntConstruction T)).trace
      (Functor.LaxMonoidal.μ (embedding T) X (𝟙_ C) ≫
        (embedding T).map ((ρ_ X).hom ≫ f ≫ (ρ_ Y).inv) ≫
          Functor.OplaxMonoidal.δ (embedding T) Y (𝟙_ C)) = (embedding T).map f := by
  rw [← embedding_preserves_trace T, T.vanishing_unit]
  simp

noncomputable section
private abbrev linearTrace := symmetricTraceOfRigid (FGModuleCat ℚ)

-- Zero feedback gives the zero crossed map in a concrete linear category.
example (X Y U : FGModuleCat ℚ) :
    hom linearTrace ((symmetricTraceOfRigid (IntConstruction linearTrace)).trace
      (Functor.LaxMonoidal.μ (embedding linearTrace) X U ≫
        (embedding linearTrace).map (0 : X ⊗ U ⟶ Y ⊗ U) ≫
          Functor.OplaxMonoidal.δ (embedding linearTrace) Y U)) = 0 := by
  rw [← embedding_preserves_trace linearTrace]
  change linearTrace.trace (0 : X ⊗ U ⟶ Y ⊗ U) ▷ (𝟙_ (FGModuleCat ℚ)) = 0
  simp [linearTrace, symmetricTraceOfRigid, SymmetricTrace.traceOfPairing]

-- Yanking remains valid after embedding, with the comparison maps present.
example (U : FGModuleCat ℚ) :
    (symmetricTraceOfRigid (IntConstruction linearTrace)).trace
      (Functor.LaxMonoidal.μ (embedding linearTrace) U U ≫
        (embedding linearTrace).map (β_ U U).hom ≫
          Functor.OplaxMonoidal.δ (embedding linearTrace) U U) =
        𝟙 ((embedding linearTrace).obj U) := by
  rw [← embedding_preserves_trace linearTrace, linearTrace.yanking]
  simp
