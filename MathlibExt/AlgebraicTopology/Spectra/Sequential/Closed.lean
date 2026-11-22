/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Adjoint structure maps for sequential spectra

In a monoidal closed category, the left structure map of a sequential
spectrum has a fixed-left transpose. This file records that transpose, its
naturality under spectrum morphisms, and the model-free predicate that all
transposes belong to a chosen morphism property.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory.SequentialSpectrum

/-- The fixed-left transpose of the structure map in level `n`. -/
noncomputable def adjointStructureMap {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [MonoidalClosed C] {K : C}
    (X : SequentialSpectrum C K) (n : ℕ) :
    X.level n ⟶ (ihom K).obj (X.level (n + 1)) :=
  MonoidalClosed.curry (X.structureMap n)

/-- Adjoint structure maps are natural under sequential-spectrum
morphisms. -/
theorem adjointStructureMap_naturality {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [MonoidalClosed C] {K : C}
    {X Y : SequentialSpectrum C K} (f : X ⟶ Y) (n : ℕ) :
    f.levelMap n ≫ adjointStructureMap Y n =
      adjointStructureMap X n ≫ (ihom K).map (f.levelMap (n + 1)) := by
  unfold adjointStructureMap
  rw [← MonoidalClosed.curry_natural_left,
    ← MonoidalClosed.curry_natural_right, f.naturality]

/-- A sequential spectrum is Omega with respect to `W` when every adjoint
structure map belongs to `W`. -/
def IsOmega {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [MonoidalClosed C] {K : C} (W : MorphismProperty C)
    (X : SequentialSpectrum C K) : Prop :=
  ∀ n, W (adjointStructureMap X n)

end CategoryTheory.SequentialSpectrum
