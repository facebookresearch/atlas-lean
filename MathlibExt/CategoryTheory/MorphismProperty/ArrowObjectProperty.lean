/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-! # The ordinary Arrow view of a morphism property

The same original morphism property is viewed as a property of ordinary
Arrow objects. Object and Hom universes remain independent. This neutral
definition does not require an accessibility or model-category interface.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- The objects of the ordinary Arrow category whose underlying arrows satisfy `W`. -/
def arrowObjectProperty (W : MorphismProperty C) : ObjectProperty (CategoryTheory.Arrow C) :=
  fun f => W f.hom

end CategoryTheory.MorphismProperty
