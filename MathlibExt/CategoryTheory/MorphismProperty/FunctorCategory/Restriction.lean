/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!# Original restriction of pointwise morphism properties -/

@[expose] public section
set_option autoImplicit false

universe uD vD uE vE uM vM

namespace CategoryTheory.MorphismProperty

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M]

/-- Actual precomposition tests the same original component at `u.obj d`. -/
theorem functorCategory_le_inverseImage_whiskeringLeft (P : MorphismProperty M) (u : D ⥤ E) :
    P.functorCategory E ≤
      (P.functorCategory D).inverseImage ((Functor.whiskeringLeft D E M).obj u) := by
  intro X Y f hf d
  exact hf (u.obj d)

end CategoryTheory.MorphismProperty
