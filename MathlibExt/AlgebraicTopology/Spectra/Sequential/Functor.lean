/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.EnrichedIndex
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation

/-!
# Sequential spectra as genuine enriched functors

The canonical carrier is the enriched functor category on the tensor-power index.
Levels and successor structure maps are derived from the actual enriched action.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory Limits
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.Sequential

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasInitial C]

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The actual enriched degree index for the suspension coordinate. -/
abbrev Index (K : C) := CategoryTheory.SequentialSpectrum.EnrichedIndex.Index K

/-- Sequential spectra are genuine enriched functors on the actual tensor-power index. -/
abbrev Spectrum (K : C) := EnrichedFunctorCat C (Index K)

/-- The object of the actual enriched functor in degree n. -/
abbrev level {K : C} (X : Spectrum K) (n : ℕ) : C :=
  X.toEnrichedFunctor.obj (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)

/-- The actual ordinary component of a genuine unit-graded spectrum map. -/
abbrev levelMap {K : C} {X Y : Spectrum K} (f : X ⟶ Y) (n : ℕ) :
    level X n ⟶ level Y n :=
  EnrichedFunctorCat.component f
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)

/-- The full uncurried enriched action, retaining the entire source Hom object. -/
abbrev action {K : C} (X : Spectrum K) (a b : Index K) :
    X.toEnrichedFunctor.obj a ⊗ (a ⟶[C] b) ⟶ X.toEnrichedFunctor.obj b :=
  MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b)

/-- The left successor map is derived through the degree-one Hom and inverse forward braid. -/
def structureMap {K : C} (X : Spectrum K) (n : ℕ) :
    K ⊗ level X n ⟶ level X (n + 1) :=
  ((CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n).inv ⊗ₘ
    𝟙 (level X n)) ≫
      (β_ (level X n)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K
          (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
          (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1)))).inv ≫
      action X (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1))

/-- Identity maps retain the actual level identities. -/
theorem levelMap_id {K : C} (X : Spectrum K) (n : ℕ) :
    levelMap (𝟙 X) n = 𝟙 (level X n) :=
  EnrichedFunctorCat.component_id X _

/-- Composition retains the actual source-first level components. -/
theorem levelMap_comp {K : C} {X Y Z : Spectrum K}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    levelMap (f ≫ g) n = levelMap f n ≫ levelMap g n :=
  EnrichedFunctorCat.component_comp f g _

/-- Genuine spectrum morphisms are determined by all their actual level maps. -/
@[ext] theorem hom_ext {K : C} {X Y : Spectrum K} {f g : X ⟶ Y}
    (h : ∀ n : ℕ, levelMap f n = levelMap g n) : f = g := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  rcases a with ⟨n⟩
  exact h n

/-- Spectrum morphisms commute with the complete original Hom-object actions. -/
theorem action_naturality {K : C} {X Y : Spectrum K} (f : X ⟶ Y) (a b : Index K) :
    action X a b ≫ EnrichedFunctorCat.component f b =
      (EnrichedFunctorCat.component f a ⊗ₘ 𝟙 (a ⟶[C] b)) ≫ action Y a b :=
  f.uncurriedNaturality a b

/-- The actual successor maps commute with every genuine spectrum morphism. -/
theorem structureMap_naturality {K : C} {X Y : Spectrum K} (f : X ⟶ Y) (n : ℕ) :
    (K ◁ levelMap f n) ≫ structureMap Y n =
      structureMap X n ≫ levelMap f (n + 1) := by
  let i := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n
  let j := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1)
  let H := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K i j
  let D : K ⟶ H :=
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n).inv
  let A := X.toEnrichedFunctor.obj i
  let B := Y.toEnrichedFunctor.obj i
  let q : A ⟶ B := EnrichedFunctorCat.component f i
  let q' := EnrichedFunctorCat.component f j
  let AX := action X i j
  let AY := action Y i j
  have hNatural : AX ≫ q' = (q ⊗ₘ 𝟙 H) ≫ AY :=
    f.uncurriedNaturality i j
  have hTensor : (𝟙 K ⊗ₘ q) ≫ (D ⊗ₘ 𝟙 B) =
      (D ⊗ₘ 𝟙 A) ≫ (𝟙 H ⊗ₘ q) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  have hBraid : (𝟙 H ⊗ₘ q) ≫ (β_ B H).inv =
      (β_ A H).inv ≫ (q ⊗ₘ 𝟙 H) := by
    simpa only [id_tensorHom, tensorHom_id] using braiding_inv_naturality_right H q
  dsimp only [structureMap]
  simp only [Category.assoc]
  change (K ◁ q) ≫ (D ⊗ₘ 𝟙 B) ≫ (β_ B H).inv ≫ AY =
    (D ⊗ₘ 𝟙 A) ≫ (β_ A H).inv ≫ AX ≫ q'
  calc
    _ = (𝟙 K ⊗ₘ q) ≫ (D ⊗ₘ 𝟙 B) ≫ (β_ B H).inv ≫ AY := by
      rw [id_tensorHom]
    _ = (D ⊗ₘ 𝟙 A) ≫ (𝟙 H ⊗ₘ q) ≫ (β_ B H).inv ≫ AY := by
      simpa only [Category.assoc] using
        congrArg (fun m => m ≫ (β_ B H).inv ≫ AY) hTensor
    _ = (D ⊗ₘ 𝟙 A) ≫ (β_ A H).inv ≫ (q ⊗ₘ 𝟙 H) ≫ AY := by
      simpa only [Category.assoc] using
        congrArg (fun m => (D ⊗ₘ 𝟙 A) ≫ m ≫ AY) hBraid
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun m => (D ⊗ₘ 𝟙 A) ≫ (β_ A H).inv ≫ m) hNatural.symm

/-- Canonical level evaluation is the existing enriched evaluation functor. -/
abbrev evaluation (K : C) (n : ℕ) : Spectrum K ⥤ C :=
  EnrichedFunctorCat.evaluation
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)

/-- Canonical free generation is the existing actual enriched free functor. -/
abbrev freeAt (K : C) (n : ℕ) : C ⥤ Spectrum K :=
  EnrichedFunctorCat.Free.functor
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)

/-- The free/evaluation adjunction is the original generic enriched adjunction. -/
abbrev freeAtEvaluationAdjunction (K : C) (n : ℕ) :
    freeAt K n ⊣ evaluation K n :=
  EnrichedFunctorCat.Free.adjunction
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)

/-- A free spectrum retains the complete coefficient tensor Hom object. -/
theorem freeAt_obj_level (K : C) (n m : ℕ) (A : C) :
    level ((freeAt K n).obj A) m =
      A ⊗ CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K m) := rfl

/-- A free spectrum map retains the complete original coefficient-tensor arrow. -/
theorem freeAt_map_levelMap (K : C) (n m : ℕ) {A B : C} (f : A ⟶ B) :
    levelMap ((freeAt K n).map f) m =
      f ▷ CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K m) :=
  EnrichedFunctorCat.Free.coefficientMap_component _ f _

end CategoryTheory.Spectra.Sequential
