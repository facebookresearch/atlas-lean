/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.Functor
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Stabilization maps on genuine enriched sequential functors

The successor transformation is derived from the actual enriched functor
structure map. The literal free transpose is natural by the existing general
mates equivalence. No stabilization map, naturality law or model is an input.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.Sequential

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [CategoryTheory.Limits.HasInitial C]

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The actual successor maps form a transformation of actual evaluation functors. -/
def structureTransformation (K : C) (n : ℕ) :
    evaluation K n ⋙ tensorLeft K ⟶ evaluation K (n + 1) where
  app X := structureMap X n
  naturality {_X _Y} f := structureMap_naturality f n

/-- The stabilization map is the literal transpose of the unit and successor map. -/
def stabilizationMap (K : C) (n : ℕ) (A : C) :
    (freeAt K (n + 1)).obj (K ⊗ A) ⟶ (freeAt K n).obj A :=
  ((freeAtEvaluationAdjunction K (n + 1)).homEquiv
    (K ⊗ A) ((freeAt K n).obj A)).symm
      ((K ◁ (freeAtEvaluationAdjunction K n).unit.app A) ≫
        structureMap ((freeAt K n).obj A) n)

/-- The complete actual adjunct is the original unit/structure composite. -/
theorem stabilizationMap_homEquiv (K : C) (n : ℕ) (A : C) :
    (freeAtEvaluationAdjunction K (n + 1)).homEquiv
      (K ⊗ A) ((freeAt K n).obj A) (stabilizationMap K n A) =
        (K ◁ (freeAtEvaluationAdjunction K n).unit.app A) ≫
          structureMap ((freeAt K n).obj A) n :=
  ((freeAtEvaluationAdjunction K (n + 1)).homEquiv
    (K ⊗ A) ((freeAt K n).obj A)).apply_symm_apply _

/-- Naturality follows from the actual general adjunction mates correspondence. -/
theorem stabilizationMap_naturality (K : C) (n : ℕ)
    {A B : C} (f : A ⟶ B) :
    (freeAt K (n + 1)).map (K ◁ f) ≫ stabilizationMap K n B =
      stabilizationMap K n A ≫ (freeAt K n).map f := by
  let β : TwoSquare (evaluation K n) (𝟭 (Spectrum K))
      (tensorLeft K) (evaluation K (n + 1)) :=
    structureTransformation K n ≫ (Functor.leftUnitor (evaluation K (n + 1))).inv
  let α : tensorLeft K ⋙ freeAt K (n + 1) ⟶ freeAt K n :=
    (mateEquiv (freeAtEvaluationAdjunction K n)
      (freeAtEvaluationAdjunction K (n + 1))).symm β ≫
        (Functor.rightUnitor (freeAt K n)).hom
  have hApp (Z : C) : α.app Z = stabilizationMap K n Z := by
    apply ((freeAtEvaluationAdjunction K (n + 1)).homEquiv
      (K ⊗ Z) ((freeAt K n).obj Z)).injective
    rw [stabilizationMap_homEquiv, Adjunction.homEquiv_unit]
    let m : tensorLeft K ⋙ freeAt K (n + 1) ⟶ freeAt K n ⋙ 𝟭 (Spectrum K) :=
      (mateEquiv (freeAtEvaluationAdjunction K n)
        (freeAtEvaluationAdjunction K (n + 1))).symm β
    have hAlpha : α.app Z = m.app Z :=
      (NatTrans.comp_app m (Functor.rightUnitor (freeAt K n)).hom Z).trans
        ((congrArg
          (fun q : (freeAt K n).obj Z ⟶ (freeAt K n).obj Z => m.app Z ≫ q)
          (Functor.rightUnitor_hom_app (freeAt K n) Z)).trans
            (Category.comp_id (m.app Z)))
    have hBeta (X : Spectrum K) : β.app X = structureMap X n :=
      (NatTrans.comp_app (structureTransformation K n)
        (Functor.leftUnitor (evaluation K (n + 1))).inv X).trans
        ((congrArg
          (fun q : (evaluation K (n + 1)).obj X ⟶
              (evaluation K (n + 1)).obj X =>
            (structureTransformation K n).app X ≫ q)
          (Functor.leftUnitor_inv_app (evaluation K (n + 1)) X)).trans
            (Category.comp_id ((structureTransformation K n).app X)))
    have hRaw :
        (tensorLeft K).map ((freeAtEvaluationAdjunction K n).unit.app Z) ≫
            β.app ((freeAt K n).obj Z) =
          (freeAtEvaluationAdjunction K (n + 1)).unit.app (K ⊗ Z) ≫
            (evaluation K (n + 1)).map (m.app Z) := by
      change
        (tensorLeft K).map ((freeAtEvaluationAdjunction K n).unit.app Z) ≫
            β.app ((freeAt K n).obj Z) =
          (freeAtEvaluationAdjunction K (n + 1)).unit.app ((tensorLeft K).obj Z) ≫
            (evaluation K (n + 1)).map
              (((mateEquiv (freeAtEvaluationAdjunction K n)
                (freeAtEvaluationAdjunction K (n + 1))).symm β).app Z)
      exact unit_mateEquiv_symm (G := tensorLeft K) (H := 𝟭 (Spectrum K))
        (freeAtEvaluationAdjunction K n)
        (freeAtEvaluationAdjunction K (n + 1)) β Z
    have hTensor :
        (tensorLeft K).map ((freeAtEvaluationAdjunction K n).unit.app Z) =
          K ◁ (freeAtEvaluationAdjunction K n).unit.app Z := rfl
    have hEntry :
        (freeAtEvaluationAdjunction K (n + 1)).unit.app (K ⊗ Z) ≫
            (evaluation K (n + 1)).map (α.app Z) =
          (freeAtEvaluationAdjunction K (n + 1)).unit.app (K ⊗ Z) ≫
            (evaluation K (n + 1)).map (m.app Z) :=
      congrArg
        (fun q : (freeAt K (n + 1)).obj (K ⊗ Z) ⟶ (freeAt K n).obj Z =>
          (freeAtEvaluationAdjunction K (n + 1)).unit.app (K ⊗ Z) ≫
            (evaluation K (n + 1)).map q) hAlpha
    have hAfterBeta :
        (tensorLeft K).map ((freeAtEvaluationAdjunction K n).unit.app Z) ≫
            β.app ((freeAt K n).obj Z) =
          (tensorLeft K).map ((freeAtEvaluationAdjunction K n).unit.app Z) ≫
            structureMap ((freeAt K n).obj Z) n :=
      congrArg
        (fun q : (evaluation K n ⋙ tensorLeft K).obj ((freeAt K n).obj Z) ⟶
            (evaluation K (n + 1)).obj ((freeAt K n).obj Z) =>
          (tensorLeft K).map ((freeAtEvaluationAdjunction K n).unit.app Z) ≫ q)
        (hBeta ((freeAt K n).obj Z))
    have hAfterTensor :
        (tensorLeft K).map ((freeAtEvaluationAdjunction K n).unit.app Z) ≫
            structureMap ((freeAt K n).obj Z) n =
          (K ◁ (freeAtEvaluationAdjunction K n).unit.app Z) ≫
            structureMap ((freeAt K n).obj Z) n :=
      congrArg
        (fun q : K ⊗ Z ⟶ (evaluation K n ⋙ tensorLeft K).obj ((freeAt K n).obj Z) =>
          q ≫ structureMap ((freeAt K n).obj Z) n) hTensor
    exact hEntry.trans (hRaw.symm.trans (hAfterBeta.trans hAfterTensor))
  have h : (freeAt K (n + 1)).map (K ◁ f) ≫ α.app B =
      α.app A ≫ (freeAt K n).map f := α.naturality f
  rw [hApp A, hApp B] at h
  exact h

/-- The original literal transpose maps form a natural transformation. -/
def stabilizationTransformation (K : C) (n : ℕ) :
    tensorLeft K ⋙ freeAt K (n + 1) ⟶ freeAt K n where
  app A := stabilizationMap K n A
  naturality {_A _B} f := stabilizationMap_naturality K n f

end CategoryTheory.Spectra.Sequential
