/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceComponentLabels

/-!
# Genuine SAME original full flagged-component projection weakness

The native nerve of EVERY complete original fixed-scalar flagged
category maps weakly to its SAME actual discrete component labels.
Original flanking, proved nondegenerate normalization, genuine paired
lifting and the actual component-label equivalence prove this statement.
No component or weak-outcome certificate is an input.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

/-- The SAME actual discrete nerve map of the full original component-label equivalence. -/
def discreteNerveMap (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerve (Discrete (ConnectedComponents (Flanking.Flanked K x y q))) ⟶
      nerve (Discrete (ConnectedComponents (Object K x y q))) :=
  CategoryTheory.nerveMap (discreteEquivalence K x y q).functor

/-- The SAME actual discrete component-label nerve map is genuinely weak. -/
theorem discreteNerveMap_weak (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (discreteNerveMap K x y q) :=
  CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
    (discreteEquivalence K x y q).functor

/-- The SAME complete original flagged-category component projection on native composable chains. -/
def projection (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerve (Object K x y q) ⟶ nerve (Discrete (ConnectedComponents (Object K x y q))) :=
  CategoryTheory.nerveMapHomDown.{u, 0, u} (projectionFunctor K x y q)

/-- Both original normalization stages retain the SAME full original projection map. -/
theorem projection_flanking (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Flanking.flankingNerveMap K x y q ≫ Normalization.flankedComponentProjection K x y q ≫
      discreteNerveMap K x y q = projection K x y q := by
  unfold Flanking.flankingNerveMap Normalization.flankedComponentProjection discreteNerveMap projection
  rw [CategoryTheory.nerveMapHomDown_nerveMap_comp, CategoryTheory.nerveMap_nerveMapHomDown_comp,
    projectionFunctor_flanking]

/-- The SAME complete original flagged-category component projection is genuinely weak for EVERY input and scalar. -/
theorem projection_weak (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (projection K x y q) := by
  rw [← projection_flanking]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ (Flanking.flankingNerveMap_weak K x y q)
    (SSet.realizationWeakEquivalences.comp_mem _ _
      (Normalization.flankedComponentProjection_weak K x y q) (discreteNerveMap_weak K x y q))

/-- The SAME complete original projection retains the original category vertex's literal component label. -/
theorem projection_vertex (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (T : Object K x y q) :
    (projection K x y q).app (op ⦋0⦌) (ComposableArrows.mk₀ T) =
      ComposableArrows.mk₀ (Discrete.mk (ConnectedComponents.mk T)) :=
  ComposableArrows.ext₀ rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
