/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntConstruction
import Mathlib.Algebra.Category.FGModuleCat.Basic

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable (T : SymmetricTrace C)

-- The construction needs a trace, not chosen dual objects in the source.
example : Category (IntConstruction T) := inferInstance

example {X Y Z W : IntConstruction T} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := Category.assoc f g h

example : (IntConstruction.embedding T).Full := inferInstance

example : (IntConstruction.embedding T).Faithful := inferInstance

-- Mixed positive/negative objects use the crossed hom type.
example (A B U V : C) (f : A ⊗ V ⟶ B ⊗ U) :
    (⟨A, U⟩ : IntConstruction T) ⟶ ⟨B, V⟩ := f

example (A U : C) :
    (𝟙 (⟨A, U⟩ : IntConstruction T)) = (𝟙 (A ⊗ U) : A ⊗ U ⟶ A ⊗ U) := rfl

-- Pin the actual wiring, in addition to exercising the category laws.
example (A B D U V W : C)
    (f : (⟨A, U⟩ : IntConstruction T) ⟶ ⟨B, V⟩)
    (g : (⟨B, V⟩ : IntConstruction T) ⟶ ⟨D, W⟩) :
    IntConstruction.hom T (f ≫ g) = T.trace (IntConstruction.exchange A W V ≫
      IntConstruction.hom T f ▷ W ≫
      IntConstruction.exchange B U W ≫ IntConstruction.hom T g ▷ U ≫ IntConstruction.exchange D V U) := rfl

example {X Y : IntConstruction T} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp
example {X Y : IntConstruction T} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by simp

example (A B D : C) (f : A ⊗ 𝟙_ C ⟶ B ⊗ 𝟙_ C)
    (g : B ⊗ 𝟙_ C ⟶ D ⊗ 𝟙_ C) : IntConstruction.compose T f g = f ≫ g := by simp

-- The embedding preserves composition and reflects equality.
example {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    (IntConstruction.embedding T).map (f ≫ g) =
      (IntConstruction.embedding T).map f ≫ (IntConstruction.embedding T).map g := by simp

example {A B : C} (f g : A ⟶ B)
    (h : (IntConstruction.embedding T).map f = (IntConstruction.embedding T).map g) :
    f = g := (IntConstruction.embedding T).map_injective h

example {A B : C}
    (f : (IntConstruction.embedding T).obj A ⟶ (IntConstruction.embedding T).obj B) :
    (IntConstruction.embedding T).map ((IntConstruction.embedding T).preimage f) = f := by simp

-- A concrete preimage can be recovered using only unitors.
example {A B : C} (f : A ⊗ 𝟙_ C ⟶ B ⊗ 𝟙_ C) :
    (IntConstruction.embedding T).map ((ρ_ A).inv ≫ f ≫ (ρ_ B).hom) = f := by
  change ((ρ_ A).inv ≫ f ≫ (ρ_ B).hom) ▷ 𝟙_ C = f
  monoidal

-- Conversion helpers remain usable without unfolding the category instance.
example {X Y : IntConstruction T}
    (f : X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative) :
    IntConstruction.hom T (IntConstruction.ofHom T f) = f := by simp

example {X Y : IntConstruction T} (f : X ⟶ Y) :
    IntConstruction.ofHom T (IntConstruction.hom T f) = f := by simp

example {X Y : IntConstruction T} (f g : X ⟶ Y)
    (h : IntConstruction.hom T f = IntConstruction.hom T g) : f = g := by
  ext
  exact h

-- An untouched right wire and an interchange of feedback loops are observable API laws.
example {A B U : C} (f : A ⊗ U ⟶ B ⊗ U) (W : C) :
    T.trace (IntConstruction.exchange A W U ≫ f ▷ W ≫
      IntConstruction.exchange B U W) = T.trace f ▷ W :=
  IntConstruction.trace_whiskerRight T f W

example {A B U V : C} (f : (A ⊗ U) ⊗ V ⟶ (B ⊗ U) ⊗ V) :
    T.trace (T.trace f) = T.trace (T.trace
      (IntConstruction.exchange A V U ≫ f ≫ IntConstruction.exchange B U V)) :=
  IntConstruction.trace_trace_exchange T f

#print axioms IntConstruction.compose_assoc
#print axioms IntConstruction.embedding


noncomputable section

-- A nontrivial concrete source, with the canonical linear trace.
example : Category (IntConstruction (symmetricTraceOfRigid (FGModuleCat ℚ))) := inferInstance

example (A B D U V W : FGModuleCat ℚ) (g : B ⊗ W ⟶ D ⊗ V) :
    IntConstruction.compose (symmetricTraceOfRigid (FGModuleCat ℚ))
      (0 : A ⊗ V ⟶ B ⊗ U) g = 0 := by
  simp [IntConstruction.compose, symmetricTraceOfRigid, SymmetricTrace.traceOfPairing]

example (A B D U V W : FGModuleCat ℚ) (f : A ⊗ V ⟶ B ⊗ U) :
    IntConstruction.compose (symmetricTraceOfRigid (FGModuleCat ℚ))
      f (0 : B ⊗ W ⟶ D ⊗ V) = 0 := by
  simp [IntConstruction.compose, symmetricTraceOfRigid, SymmetricTrace.traceOfPairing]

-- Closing a cup/cap-shaped pair computes dimension, not an identity map.
example (U : FGModuleCat ℚ) :
    ((ρ_ (𝟙_ (FGModuleCat ℚ))).inv ≫
      IntConstruction.compose (symmetricTraceOfRigid (FGModuleCat ℚ))
        (β_ (𝟙_ (FGModuleCat ℚ)) U).hom (β_ U (𝟙_ (FGModuleCat ℚ))).hom ≫
      (ρ_ (𝟙_ (FGModuleCat ℚ))).hom).hom.hom (1 : ℚ) =
      (Module.finrank ℚ U : ℚ) := by
  have h : (ρ_ (𝟙_ (FGModuleCat ℚ))).inv ≫
      IntConstruction.compose (symmetricTraceOfRigid (FGModuleCat ℚ))
        (β_ (𝟙_ (FGModuleCat ℚ)) U).hom (β_ U (𝟙_ (FGModuleCat ℚ))).hom ≫
      (ρ_ (𝟙_ (FGModuleCat ℚ))).hom =
      η_ U (Uᘁ) ≫ (β_ U (Uᘁ)).hom ≫ ε_ U (Uᘁ) := by
    simp only [IntConstruction.compose, symmetricTraceOfRigid,
      SymmetricTrace.traceOfPairing, IntConstruction.exchange,
      braiding_tensorUnit_left, braiding_tensorUnit_right]
    monoidal
  rw [h]
  change (contractLeft ℚ U)
    ((TensorProduct.comm ℚ U (Module.Dual ℚ U)) (coevaluation ℚ U 1)) = _
  classical
  rw [coevaluation_apply_one]
  simp only [map_sum, TensorProduct.comm_tmul, contractLeft_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self_apply, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact_mod_cast (Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace ℚ U)).symm
