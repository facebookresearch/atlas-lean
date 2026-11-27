/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# Two parallel comparison morphisms

In a category `C`, a pair of comparison arrows consists of source and
target objects and two parallel morphisms between them. Morphisms with
fixed endpoints give such a pair without changing either endpoint.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe uC vC
open CategoryTheory

namespace CategoryTheory

/-- In a category `C`, comparison-arrow data consist of objects
`source`, `target` and two morphisms `left`, `right : source → target`.
The two arrows share both endpoints. -/
structure ComparisonArrows {C : Type uC} [Category.{vC} C] where
  /-- For a pair of comparison arrows in a category `C`, `source` is
the common domain object of the two parallel morphisms
`left`, `right : source → target`. -/
  source : C
  /-- For a pair of comparison arrows in a category `C`, `target` is
the common codomain object of the two parallel morphisms
`left`, `right : source → target`. -/
  target : C
  /-- For comparison-arrow data in a category `C`, `left` is the first
morphism from the specified common source object to the specified
common target object. -/
  left : source ⟶ target
  /-- For comparison-arrow data in a category `C`, `right` is the second
morphism from the specified common source object to the specified
common target object. -/
  right : source ⟶ target

/-- For objects `X`, `Y` of a category `C` and parallel maps
`l`, `r : X → Y`, the resulting comparison-arrow pair has source
`X`, target `Y`, and its two morphisms are precisely `l` and `r`. -/
def comparisonArrowsOfMaps {C : Type uC} [Category.{vC} C]
    {X Y : C} (l r : X ⟶ Y) : ComparisonArrows (C := C) :=
  ⟨X, Y, l, r⟩

end CategoryTheory
