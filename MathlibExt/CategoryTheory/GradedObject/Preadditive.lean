/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import MathlibExt.CategoryTheory.Pi.Preadditive

/-!
# The canonical preadditive structure of graded objects

The native graded-object type synonym inherits the existing pointwise Pi
hom groups. Its native coproduct total is additive through the original
coprojection equations. These instances use no finite-fiber or exactness
premise. The grading, object and Hom universes remain independent.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe w w' v u

namespace GradedObject

variable {C : Type u} [Category.{v} C]

section Additive

variable [Preadditive C]

/-- The native graded-object type synonym has the pointwise preadditive structure. -/
instance gradedObjectPreadditive (β : Type w) : Preadditive (GradedObject β C) :=
  inferInstanceAs (Preadditive (β → C))

/-- The native coproduct total functor is additive by its actual coprojection equations. -/
instance gradedObjectTotalAdditive (β : Type) [HasCoproducts.{0} C] :
    (GradedObject.total β C).Additive where
  map_add {X Y f g} := by
    change Limits.Sigma.map (fun i => f i + g i) =
      Limits.Sigma.map f + Limits.Sigma.map g
    apply Limits.Sigma.hom_ext
    intro i
    simp only [Limits.Sigma.ι_map, Preadditive.comp_add, Preadditive.add_comp]

end Additive

end GradedObject

end CategoryTheory
