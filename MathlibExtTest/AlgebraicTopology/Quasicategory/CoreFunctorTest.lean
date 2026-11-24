/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.CoreFunctor

/-!
# Public core-functor clients on arbitrary simplicial sets
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace SSet

/-- The bundled object is the literal equivalence-edge core. -/
example (X : SSet.{u}) : coreFunctor.obj X = (core X : SSet.{u}) :=
  coreFunctor_obj X

/-- The bundled arrow is the literal native restriction. -/
example {X Y : SSet.{u}} (f : X ⟶ Y) :
    coreFunctor.map f = core.map f := coreFunctor_map f

/-- Its arrow action commutes with the actual core inclusions. -/
example {X Y : SSet.{u}} (f : X ⟶ Y) :
    coreFunctor.map f ≫ (core Y).ι = (core X).ι ≫ f := by
  rw [coreFunctor_map, core.map_ι]

/-- Composition in the functor produces the expected ambient composite
after including the target core. -/
example {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (coreFunctor.map f ≫ coreFunctor.map g) ≫ (core Z).ι =
      (core X).ι ≫ f ≫ g := by
  rw [← coreFunctor.map_comp, coreFunctor_map, core.map_ι]

end SSet
