/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

/-!
# Nondegenerate chains in opposite posets

A nondegenerate simplex of the nerve of the opposite of a poset has a strictly
decreasing vertex function in the original poset. The comparison uses the
order-dual equivalence and the category structure induced by the given order.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u

namespace PartialOrder

variable {P : Type u} [PartialOrder P]

/-- Nondegenerate opposite-poset nerve chains have strictly decreasing given vertices. -/
theorem nerve_op_nonDegenerate_iff_strictAnti {n : ℕ}
    (F : ComposableArrows Pᵒᵖ n) :
    F ∈ (nerve Pᵒᵖ).nonDegenerate n ↔
      StrictAnti (fun i ↦ (F.obj i).unop) := by
  let e := orderDualEquivalence P
  let G : ComposableArrows Pᵒᵈ n := F ⋙ e.inverse
  have hround : (nerveMap e.functor).app (op (SimplexCategory.mk n)) G = F :=
    ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)
  have he : F ∈ (nerve Pᵒᵖ).nonDegenerate n ↔
      G ∈ (nerve Pᵒᵈ).nonDegenerate n := by
    constructor
    · intro hF
      by_contra hG
      have hG' : G ∈ (nerve Pᵒᵈ).degenerate n :=
        (SSet.mem_degenerate_iff_notMem_nonDegenerate (nerve Pᵒᵈ) G).mpr hG
      have h := SSet.degenerate_app_apply hG' (nerveMap e.functor)
      rw [hround] at h
      exact hF h
    · intro hG
      change (nerveMap e.inverse).app (op (SimplexCategory.mk n)) F ∈
        (nerve Pᵒᵈ).nonDegenerate n at hG
      exact SSet.nonDegenerate_of_app_apply (nerveMap e.inverse) hG
  exact he.trans (mem_nerve_nonDegenerate_iff_strictMono G)

end PartialOrder

end
