/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.MorphismProperty.ArrowObjectProperty

/-! # Direct neutral clients of the original ordinary Arrow view

These clients import the lightweight API itself. No accessibility or model
module is needed to retain the original maps and independent universes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v u' v'

open CategoryTheory

namespace CategoryTheory.MorphismProperty.ArrowObjectPropertyTest

variable {C : Type u} [Category.{v} C]

/-- The whole original Arrow view uses its original underlying map. -/
theorem wholeOriginalArrow (W : MorphismProperty C) (a : CategoryTheory.Arrow C) :
    W.arrowObjectProperty a ↔ W a.hom := Iff.rfl

/-- A given original map is the same predicate in its ordinary Arrow object. -/
theorem originalMap (W : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    W.arrowObjectProperty (CategoryTheory.Arrow.mk f) ↔ W f := Iff.rfl

/-- Pulling a predicate along a real functor commutes with the same Arrow view. -/
theorem originalFunctorMap {D : Type u'} [Category.{v'} D]
    (F : D ⥤ C) (W : MorphismProperty C) (a : CategoryTheory.Arrow D) :
    (W.inverseImage F).arrowObjectProperty a ↔
      W.arrowObjectProperty (F.mapArrow.obj a) := Iff.rfl

/-- An independently larger object representation does not enlarge the given Hom universe. -/
theorem independentObjectHom {D : Type 1} [Category.{0} D]
    (W : MorphismProperty D) (a : CategoryTheory.Arrow D) :
    W.arrowObjectProperty a ↔ W a.hom := Iff.rfl

end CategoryTheory.MorphismProperty.ArrowObjectPropertyTest
