/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementCardinalEnvelope
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGenerators
import MathlibExt.CategoryTheory.NatTrans.MonoFactorization
import Mathlib.Basic.Countable.Basic

/-!
# Total-point bounds for the literal Reedy boundaries

The target of every literal two-dimensional Reedy boundary is the product of
two standard simplices.  Its total point type is countable, including either
zero boundary dimension.  The boundary map is an actual Reedy cofibration and
therefore a monomorphism, so its source has no more total points than its
target.  The fixed local-replacement envelope absorbs both endpoints.
-/

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace SimplicialSpace.ReedyGeneratingFamilies

private def totalPointsEquivSigma (X : SimplicialSpace.{u}) :
    (Functor.uncurry.obj X.diagram).Elements ≃
      Σ r : SimplexCategoryᵒᵖ, Σ s : SimplexCategoryᵒᵖ, (X.diagram.obj r).obj s where
  toFun x := ⟨x.obj.1, x.obj.2, x.val⟩
  invFun x := Functor.elementsMk _ (x.1, x.2.1) x.2.2
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨r, s, x⟩; rfl

private theorem simplexCategory_countable : Countable SimplexCategory :=
  (show Function.Injective SimplexCategory.len from by
    intro a b h
    rw [← SimplexCategory.mk_len a, ← SimplexCategory.mk_len b, h]).countable

private theorem simplexCategory_op_countable : Countable SimplexCategoryᵒᵖ := by
  let _ : Countable SimplexCategory := simplexCategory_countable
  exact (Opposite.unop_injective :
    Function.Injective (unop : SimplexCategoryᵒᵖ → SimplexCategory)).countable

/-- A literal Reedy boundary is a monomorphism in the original
simplicial-space category. -/
theorem boundaryFamily_mono (b : BoundaryIndex) :
    Mono (boundaryFamily.{u} b).hom := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  have hmem : I.{u} (boundaryFamily.{u} b).hom :=
    MorphismProperty.ofHoms.mk b
  have hleft : I.{u}.rlp.llp (boundaryFamily.{u} b).hom :=
    I.{u}.le_llp_rlp _ hmem
  rw [I_rlp_eq_trivialFibrations] at hleft
  rw [trivialFibrations_llp SimplicialSpace.{u}] at hleft
  exact (ReedyModel.cofibration_iff _).1
    ((HomotopicalAlgebra.cofibration_iff _).2 hleft)

/-- The full target total-point type of every literal Reedy boundary is
countable. -/
theorem boundaryFamily_target_points_le_aleph0 (b : BoundaryIndex) :
    Cardinal.mk (Functor.uncurry.obj
      (boundaryFamily.{u} b).right.diagram).Elements ≤ ℵ₀ := by
  let _ : Countable SimplexCategoryᵒᵖ := simplexCategory_op_countable
  let _ : ∀ r : SimplexCategoryᵒᵖ, ∀ s : SimplexCategoryᵒᵖ,
      Countable (((boundaryFamily.{u} b).right.diagram.obj r).obj s) :=
    fun r s => by
      change Countable
        (((Δ[b.1] : SSet.{u}).obj r) × ((Δ[b.2] : SSet.{u}).obj s))
      infer_instance
  let _ : Countable (Functor.uncurry.obj
      (boundaryFamily.{u} b).right.diagram).Elements :=
    (totalPointsEquivSigma (boundaryFamily.{u} b).right).injective.countable
  exact Cardinal.mk_le_aleph0

/-- The total points of a literal Reedy boundary source inject into those of
its target. -/
theorem boundaryFamily_source_points_le_target (b : BoundaryIndex) :
    Cardinal.mk (Functor.uncurry.obj
        (boundaryFamily.{u} b).left.diagram).Elements ≤
      Cardinal.mk (Functor.uncurry.obj
        (boundaryFamily.{u} b).right.diagram).Elements := by
  let F := SimplicialSpace.toPresheaf.{u}
  let _ : Mono (boundaryFamily.{u} b).hom := boundaryFamily_mono b
  let _ : F.PreservesMonomorphisms := inferInstance
  calc
    _ = Cardinal.mk (F.obj (boundaryFamily.{u} b).left).Elements :=
      mk_totalPoints_toPresheaf _
    _ ≤ Cardinal.mk (F.obj (boundaryFamily.{u} b).right).Elements :=
      Functor.mk_elements_le_of_mono (F.map (boundaryFamily.{u} b).hom)
    _ = _ := (mk_totalPoints_toPresheaf _).symm

end SimplicialSpace.ReedyGeneratingFamilies

namespace SimplicialSpace.LocalReplacementCardinalEnvelope

variable {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]

/-- The stable envelope bounds both literal endpoints of every Reedy boundary,
including both zero-dimensional cases. -/
theorem boundaryFamily_endpoint_points_le (e : LocalReplacementCardinalEnvelope κ)
    (b : ReedyGeneratingFamilies.BoundaryIndex) :
    Cardinal.mk (Functor.uncurry.obj
        (ReedyGeneratingFamilies.boundaryFamily.{u} b).left.diagram).Elements ≤ e.γ ∧
      Cardinal.mk (Functor.uncurry.obj
        (ReedyGeneratingFamilies.boundaryFamily.{u} b).right.diagram).Elements ≤ e.γ := by
  have hright :=
    (ReedyGeneratingFamilies.boundaryFamily_target_points_le_aleph0 b).trans
      e.aleph0_le_γ
  exact ⟨(ReedyGeneratingFamilies.boundaryFamily_source_points_le_target b).trans
    hright, hright⟩

end SimplicialSpace.LocalReplacementCardinalEnvelope
