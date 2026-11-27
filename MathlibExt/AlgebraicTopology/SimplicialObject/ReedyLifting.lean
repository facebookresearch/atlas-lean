/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyStructure
public import MathlibExt.CategoryTheory.Reedy.Lifting
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Lifting between degreewise Reedy morphism properties

A morphism of simplicial objects whose relative latching maps lie in `P` lifts against a morphism
whose relative matching maps lie in `Q` whenever `P ≤ Q.llp`. This is the lifting theorem of the
generic Reedy structure, `ReedyStructure.Lifting.hasLiftingProperty`, for `SimplexCategoryᵒᵖ`:
the generic latching and matching corners are the relative latching and matching maps up to
isomorphism of arrows (`latchingCornerArrowIso`, `matchingCornerArrowIso`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Degreewise left Reedy maps lift against degreewise right Reedy maps whenever the
underlying morphism properties have the corresponding lifting relation. -/
theorem reedyLeft_le_llp_reedyRight (P Q : MorphismProperty C)
    [HasPushouts C] [HasPullbacks C]
    [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
    [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
    (hPQ : P ≤ Q.llp) :
    reedyLeft P ≤ (reedyRight Q).llp := by
  intro A B i hi E F p hp
  apply CategoryTheory.ReedyStructure.Lifting.hasLiftingProperty (r := reedyStructure)
  intro a
  let _ : HasLiftingProperty (relativeLatchingMap i a.unop.len)
      (relativeMatchingMap p a.unop.len) := hPQ _ (hi _) _ (hp _)
  let _ : HasLiftingProperty (reedyStructure.latchingCorner i (op ⦋a.unop.len⦌))
      (relativeMatchingMap p a.unop.len) :=
    HasLiftingProperty.of_arrow_iso_left (latchingCornerArrowIso i a.unop.len).symm _
  exact HasLiftingProperty.of_arrow_iso_right (reedyStructure.latchingCorner i (op ⦋a.unop.len⦌))
    (matchingCornerArrowIso p a.unop.len).symm

end CategoryTheory.SimplicialObject
