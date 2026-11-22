/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.Functor
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Closed successor maps of genuine enriched sequential functors

The transpose uses the actual successor map of the enriched functor carrier.
Its naturality follows from the existing successor naturality and the chosen
closed adjunction. The Omega predicate records a chosen arrow property.
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

/-- The fixed-left transpose of the actual enriched-functor successor map. -/
def adjointStructureMap {K : C} (X : Spectrum K) (n : ℕ) :
    level X n ⟶ (ihom K).obj (level X (n + 1)) :=
  MonoidalClosed.curry (structureMap X n)

/-- Uncurrying retains the complete actual successor map. -/
theorem adjointStructureMap_uncurry {K : C} (X : Spectrum K) (n : ℕ) :
    MonoidalClosed.uncurry (adjointStructureMap X n) = structureMap X n :=
  MonoidalClosed.uncurry_curry (structureMap X n)

/-- Actual spectrum morphisms commute with the fixed-left transpose. -/
theorem adjointStructureMap_naturality {K : C} {X Y : Spectrum K}
    (f : X ⟶ Y) (n : ℕ) :
    levelMap f n ≫ adjointStructureMap Y n =
      adjointStructureMap X n ≫ (ihom K).map (levelMap f (n + 1)) := by
  unfold adjointStructureMap
  rw [← MonoidalClosed.curry_natural_left,
    ← MonoidalClosed.curry_natural_right, structureMap_naturality f n]

/-- Every actual successor transpose belongs to the selected arrow property. -/
def IsOmega {K : C} (W : MorphismProperty C) (X : Spectrum K) : Prop :=
  ∀ n : ℕ, W (adjointStructureMap X n)

end CategoryTheory.Spectra.Sequential
