/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.FiberedCategory.DiscreteFiber

/-!
# The original discrete inclusion uses the general strict-fiber API

The legacy constructor and discrete equivalence keep their given source,
base and full fiber morphisms. Their functor is exactly the neutral general
inclusion, including the former explicit instance-argument slot.
-/

public section

noncomputable section

open CategoryTheory

universe uA vA uD vD

namespace MathlibExtTest.FiberToStructuredArrow

variable {A : Type uA} [catA : Category.{vA} A]
  {D : Type uD} [catD : Category.{vD} D] [discreteD : IsDiscrete D]

/-- The old constructor and equivalence have the same full object and morphism action. -/
theorem discrete_legacy_and_equivalence_use_general (F : A ⥤ D) (d : D)
    {a b : F.Fiber d} (f : a ⟶ b) :
    (@Functor.fiberToStructuredArrowOfIsDiscrete A catA D catD discreteD F d) =
        Functor.fiberToStructuredArrow (p := F) d ∧
      (Functor.fiberEquivalenceStructuredArrowOfIsDiscrete F d).functor =
        Functor.fiberToStructuredArrow (p := F) d ∧
      ((Functor.fiberToStructuredArrowOfIsDiscrete F d).map f).right = f.val := by
  refine ⟨rfl, rfl, ?_⟩
  exact Functor.fiberToStructuredArrowOfIsDiscrete_map_right F d f

#print axioms discrete_legacy_and_equivalence_use_general

end MathlibExtTest.FiberToStructuredArrow
