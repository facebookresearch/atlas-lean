/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Shapes
public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSlice
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# The original internal pullback comparison

A coherent square is an actual map from the nerve of the diamond.
Its native pullback condition tests every boundary against the literal
over-slice restriction to the cospan. This is the internal limiting-cone
condition; it uses the original higher cells in the ambient simplicial set.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.NativePullback

variable {X : SSet.{u}}

/-- The original square-to-cospan over-slice restriction. -/
abbrev comparison (q : squareShape.{u} ⟶ X) :
    sliceOver X q ⟶ sliceOver X (cospanInclusion ≫ q) :=
  sliceOver.restrict X q cospanInclusion

/-- A coherent square is internally cartesian when its original
comparison has every boundary lift, including dimension zero. -/
def IsPullbackSquare (q : squareShape.{u} ⟶ X) : Prop :=
  ∀ m : ℕ, HasLiftingProperty (boundary.{u} m).ι (comparison q)

/-- The predicate exposes the exact original comparison in every dimension. -/
theorem isPullbackSquare_iff (q : squareShape.{u} ⟶ X) :
    IsPullbackSquare q ↔ ∀ m : ℕ, HasLiftingProperty (boundary.{u} m).ι
      (sliceOver.restrict X q cospanInclusion) :=
  Iff.rfl

end SSet.NativePullback
