/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentEnrichment

/-!
# The SAME original full-component source functor

Every source simplicial map gives an actual enriched functor on the
complete original flagged components. Its objects, full Hom maps,
identities and compositions retain the literal original source map.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

private theorem same_input {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (N : SSet.OriginalNecklace.Data) {i j : N.object.{u} ⟶ K}
    (hi₀ : SSet.yonedaEquiv (N.source ≫ i) = x)
    (hi₁ : SSet.yonedaEquiv (N.target ≫ i) = y)
    (hj₀ : SSet.yonedaEquiv (N.source ≫ j) = x)
    (hj₁ : SSet.yonedaEquiv (N.target ≫ j) = y)
    (c : (OriginalBead.TerminalFlag.coefficientObject.{u} N.dimension).obj q)
    (hc : ∀ k ∈ N.joints, ULift.up.{u} k ∈ (c.obj 0).I) (h : i = j) :
    (Object.mk N i hi₀ hi₁ c hc : Object K x y q) = Object.mk N j hj₀ hj₁ c hc := by
  cases h
  rfl

/-- The SAME original source map takes the zero necklace to its original vertex image. -/
theorem sourceObject_unit {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    sourceObject f (unit K q x) = unit L q (f.app (op ⦋0⦌) x) := by
  apply same_input
  have h : SSet.yonedaEquiv.symm x ≫ f = SSet.yonedaEquiv.symm (f.app (op ⦋0⦌) x) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun e => (SSet.OriginalNecklace.complex Point.data.joints).ι ≫ e) h)

/-- The complete SAME original source identity square on actual component Homs. -/
theorem identity_source {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) :
    identity K x ≫ sourceMap f x x = identity L (f.app (op ⦋0⦌) x) := by
  ext q p
  exact congrArg ConnectedComponents.mk (sourceObject_unit f x q)

/-- Every SAME original source simplicial map gives its actual full-component enriched functor. -/
def sourceFunctor {K L : SSet.{u}} (f : K ⟶ L) : category K ⟶ category L where
  obj x := f.app (op ⦋0⦌) x
  map := sourceMap f
  map_id := identity_source f
  map_comp := composition_source f

/-- The full original source functor retains precisely the SAME individual original vertex map. -/
theorem sourceFunctor_obj {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) :
    (sourceFunctor f).obj x = f.app (op ⦋0⦌) x := rfl

/-- The full original source functor retains its SAME actual component-simplicial-set Hom map. -/
theorem sourceFunctor_map {K L : SSet.{u}} (f : K ⟶ L) (x y : K _⦋0⦌) :
    (sourceFunctor f).map x y = sourceMap f x y := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
