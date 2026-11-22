/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.BoundedArrowRepresentatives
import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakEquivalences

/-!
# Representatives of total-bounded Rezk weak arrows

The literal property includes both original total endpoint bounds and genuine
weakness against every same-universe complete Segal target. Native essential
smallness supplies a Type-u family inside this exact property, including
arbitrary nonmonic weak arrows.
-/

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits

namespace SimplicialSpace

/-- Original Rezk weak arrows whose two endpoint total-point types are bounded
by γ. -/
def boundedRezkWeakArrows (γ : Cardinal.{u}) :
    ObjectProperty (Arrow SimplicialSpace.{u}) := fun a =>
  Cardinal.mk (Functor.uncurry.obj a.left.diagram).Elements ≤ γ ∧
    Cardinal.mk (Functor.uncurry.obj a.right.diagram).Elements ≤ γ ∧
      rezkWeakEquivalences a.hom

/-- The original total-γ-bounded Rezk weak arrows admit a Type-u family of
representatives lying in the same property. Every original arrow has an actual
whole Arrow isomorphism to one representative. -/
theorem exists_boundedRezkWeakArrow_representatives (γ : Cardinal.{u}) :
    ∃ (ι : Type u) (r : ι → Arrow SimplicialSpace.{u}),
      (∀ i, boundedRezkWeakArrows γ (r i)) ∧
        ∀ a, boundedRezkWeakArrows γ a →
          ∃ i, Nonempty (a ≅ r i) := by
  apply exists_bounded_arrow_representatives γ (boundedRezkWeakArrows γ)
  intro a ha
  exact ⟨ha.1, ha.2.1⟩

end SimplicialSpace
