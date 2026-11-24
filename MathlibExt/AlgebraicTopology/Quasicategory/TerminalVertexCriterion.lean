/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.TerminalSliceCriterion

/-!
# Native slice characterizations of the canonical terminal predicate

The existing full-boundary/cone comparison supplies these characterizations
for every simplicial set. The neutral and WalkingAdjunction names refer to
one predicate and the same original proofs.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial
universe u

namespace SSet

/-- Compatibility name for the existing original slice-boundary characterization. -/
theorem isTerminalVertex_iff {X : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X) :
    IsTerminalVertex x ↔ ∀ n : ℕ, HasLiftingProperty (boundary n).ι (sliceOver.proj X x) :=
  WalkingAdjunction.rightTerminalVertex_iff_slice_boundary x

/-- Compatibility name for the existing original generating-boundary characterization. -/
theorem isTerminalVertex_iff_I_rlp {X : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X) :
    IsTerminalVertex x ↔ modelCategoryQuillen.I.rlp (sliceOver.proj X x) :=
  WalkingAdjunction.rightTerminalVertex_iff_slice_rlp_I x

end SSet
