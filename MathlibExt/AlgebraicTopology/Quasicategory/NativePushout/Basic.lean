/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePushout.Shapes
public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSlice
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# The original internal pushout comparison

A coherent square is a map from the full nerve of the native diamond.
Its native pushout condition tests every boundary against the original
under-slice restriction to the walking span, including dimension zero.
The definition uses the original square and all its higher simplices.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.NativePushout

variable {X : SSet.{u}}

/-- The actual original square-to-span under-slice restriction. -/
abbrev comparison (q : squareShape.{u} ⟶ X) :
    sliceUnder X q ⟶ sliceUnder X (spanInclusion ≫ q) :=
  sliceUnder.restrict X q spanInclusion

/-- A coherent square is internally cocartesian when its original comparison
has every original boundary lift. -/
def IsPushoutSquare (q : squareShape.{u} ⟶ X) : Prop :=
  ∀ n : ℕ, HasLiftingProperty (boundary n).ι (comparison q)

/-- The native pushout condition keeps the exact original comparison in every dimension. -/
theorem isPushoutSquare_iff (q : squareShape.{u} ⟶ X) :
    IsPushoutSquare q ↔ ∀ n : ℕ,
      HasLiftingProperty (boundary n).ι (sliceUnder.restrict X q spanInclusion) := Iff.rfl

end SSet.NativePushout
