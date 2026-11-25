/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import MathlibExt.CategoryTheory.Pi.Preadditive

/-!
# Preadditivity of graded objects

The hom groups of graded objects are defined pointwise, and the
coproduct total functor is additive. The grading, object and morphism
universes are independent.
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
