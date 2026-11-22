/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceNondegenerateComponents

/-!
# Genuine SAME original flanked-component augmentation weakness

The actual native nerve of EVERY original flanked-necklace category
maps weakly to its SAME discrete connected-component labels. The map
is the original component projection, with no component-contractibility
outcome assumed. The genuine normalization and nondegenerate component
equivalence prove its weakness.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Normalization

open Flanking

/-- The SAME full original native flanked-category component projection. -/
def flankedComponentProjection (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerve (Flanked K x y q) ⟶ nerve (Discrete (ConnectedComponents (Flanked K x y q))) :=
  CategoryTheory.nerveMapHomDown.{u, 0, u} (componentProjectionFunctor K x y q)

/-- The actual original normalization triangle retains the SAME complete component projection map. -/
theorem normalization_componentProjection (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerveMap K x y q ≫ componentNerveMap K x y q = flankedComponentProjection K x y q := by
  unfold nerveMap componentNerveMap flankedComponentProjection
  rw [CategoryTheory.nerveMap_nerveMapHomDown_comp, normalization_componentFunctor]

/-- The SAME original full flanked-category component projection is genuinely weak for EVERY input and scalar. -/
theorem flankedComponentProjection_weak (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (flankedComponentProjection K x y q) := by
  rw [← normalization_componentProjection]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ (nerveMap_weak K x y q)
    (componentNerveMap_weak K x y q)

/-- The SAME original projection assigns the full original category vertex its literal original component label. -/
theorem flankedComponentProjection_vertex (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (T : Flanked K x y q) :
    (flankedComponentProjection K x y q).app (op ⦋0⦌) (ComposableArrows.mk₀ T) =
      ComposableArrows.mk₀ (Discrete.mk (ConnectedComponents.mk T)) :=
  ComposableArrows.ext₀ rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Normalization
