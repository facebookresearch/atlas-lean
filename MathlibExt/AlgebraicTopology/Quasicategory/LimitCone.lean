/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.Quasicategory.TerminalVertexCriterion
public import MathlibExt.AlgebraicTopology.SimplicialSet.IteratedJoinSlice

/-!
# Native limiting cones

The limit condition for a whole cone tests every boundary against the
original cone-to-diagram over-slice restriction. The actual iterated-slice
isomorphism identifies it with terminality of the given cone point.
For a quasicategory this is the usual infinity-categorical limit condition.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

variable {X K : SSet.{u}}

/-- A whole original left cone is limiting when its cone-to-diagram
restriction lifts every original standard boundary. -/
def IsLimitCone (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X) : Prop :=
  ∀ m : ℕ, HasLiftingProperty (boundary.{u} m).ι
    (sliceOver.restrict X q (joinInr Δ[0] K))

/-- The limiting condition is terminality of the original cone point
in the original diagram over-slice, with every dimension retained. -/
theorem isLimitCone_iff_isTerminalVertex (f : K ⟶ X)
    (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X) (hq : joinInr Δ[0] K ≫ q = f) :
    IsLimitCone q ↔ IsTerminalVertex (sliceOver.conePoint f q hq) := by
  rw [isTerminalVertex_iff]
  unfold IsLimitCone
  apply forall_congr'
  intro m
  exact HasLiftingProperty.iff_of_arrow_iso_right (boundary m).ι
    (sliceOver.coneRestrictionArrowIso f q hq)

end SSet
