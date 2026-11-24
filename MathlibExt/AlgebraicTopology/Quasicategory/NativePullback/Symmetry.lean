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

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceIndexIso

/-!
# Branch symmetry of canonical coherent squares

The standard walking-cospan branch swap extends through WithInitial.
Its actual nerve isomorphisms transport the all-boundary internal
pullback condition and exchange the original horizontal and vertical sides.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet.NativePullback

/-- The native walking-cospan swap, lifted to the common simplicial universe. -/
def swapCospanFunctor : CospanObjects.{u} ⥤ CospanObjects.{u} :=
  ULift.downFunctor ⋙ (WidePullbackShape.equivalenceOfEquiv WalkingPair WalkingPair.swap).functor ⋙
    ULift.upFunctor

/-- Exchange the two branches of the standard walking cospan. -/
def swapCospanObjects (v : CospanObjects.{u}) : CospanObjects.{u} := swapCospanFunctor.obj v

theorem swapCospanObjects_twice (v : CospanObjects.{u}) :
    swapCospanObjects (swapCospanObjects v) = v := by
  rcases v with ⟨v⟩
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

/-- The standard WithInitial map extends the walking-cospan swap to the complete diamond. -/
def swapFunctor : DiamondObjects.{u} ⥤ DiamondObjects.{u} := WithInitial.map swapCospanFunctor

/-- Exchange the two square branches while fixing its adjoined initial object and common target. -/
def swapObjects (v : DiamondObjects.{u}) : DiamondObjects.{u} := swapFunctor.obj v

theorem swapObjects_twice (v : DiamondObjects.{u}) : swapObjects (swapObjects v) = v := by
  cases v with
  | star => rfl
  | of v => exact congrArg WithInitial.of (swapCospanObjects_twice v)

/-- The actual coordinate exchange retains every original square simplex. -/
def squareSwapIso : squareShape.{u} ≅ squareShape.{u} where
  hom := nerveMap swapFunctor
  inv := nerveMap swapFunctor
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact swapObjects_twice (s.obj i)
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact swapObjects_twice (s.obj i)

/-- The actual coordinate exchange retains every original cospan simplex. -/
def cospanSwapIso : cospanShape.{u} ≅ cospanShape.{u} where
  hom := nerveMap swapCospanFunctor
  inv := nerveMap swapCospanFunctor
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact swapCospanObjects_twice (s.obj i)
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact swapCospanObjects_twice (s.obj i)

/-- The given original inclusion commutes with both coordinate exchanges. -/
theorem cospanInclusion_swap :
    cospanInclusion ≫ squareSwapIso.hom =
      cospanSwapIso.hom ≫ cospanInclusion := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  rfl

/-- The original side maps are exchanged, including all their degeneracies. -/
theorem topEdge_swap : topEdge.{u} ≫ squareSwapIso.hom = leftEdge := by
  erw [topEdge, edge, yonedaEquiv_symm_comp]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

theorem bottomEdge_swap : bottomEdge.{u} ≫ squareSwapIso.hom = rightEdge := by
  erw [bottomEdge, edge, yonedaEquiv_symm_comp]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

theorem leftEdge_swap : leftEdge.{u} ≫ squareSwapIso.hom = topEdge := by
  erw [leftEdge, edge, yonedaEquiv_symm_comp]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

theorem rightEdge_swap : rightEdge.{u} ≫ squareSwapIso.hom = bottomEdge := by
  erw [rightEdge, edge, yonedaEquiv_symm_comp]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- Coordinate exchange preserves the full original internal pullback condition. -/
theorem isPullbackSquare_swap_iff {X : SSet.{u}} (q : squareShape.{u} ⟶ X) :
    IsPullbackSquare q ↔ IsPullbackSquare (squareSwapIso.hom ≫ q) := by
  unfold IsPullbackSquare
  apply forall_congr'
  intro m
  exact sliceOver.hasLiftingProperty_restrictionIndex_iff X q cospanInclusion
    cospanInclusion squareSwapIso cospanSwapIso cospanInclusion_swap (boundary m).ι

end SSet.NativePullback
