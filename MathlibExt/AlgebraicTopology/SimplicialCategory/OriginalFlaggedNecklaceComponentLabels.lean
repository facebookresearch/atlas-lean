/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceFlankedComponentWeak

/-!
# SAME original full and flanked component labels

The actual original flanking and inclusion functors induce inverse maps
on the SAME original connected-component sets. The inverse equations
come from the original full native inclusion natural transformations,
without assuming any component or comparison outcome.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

open Flanking

/-- The SAME original full-subcategory inclusion on actual component labels. -/
def inclusion (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    ConnectedComponents (Flanked K x y q) → ConnectedComponents (Object K x y q) :=
  (inclusionFunctor K x y q).mapConnectedComponents

/-- The SAME original whole flanking functor on actual component labels. -/
def flanking (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    ConnectedComponents (Object K x y q) → ConnectedComponents (Flanked K x y q) :=
  (toFlanked K x y q).mapConnectedComponents

/-- The actual original restricted inclusion gives the SAME original component inverse equation. -/
theorem flanking_inclusion (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (c : ConnectedComponents (Flanked K x y q)) : flanking K x y q (inclusion K x y q c) = c := by
  induction c using Quotient.inductionOn' with
  | h T =>
    exact Quotient.sound' (Zigzag.of_hom ((flankedInclusion K x y q).app T))

/-- The actual original full inclusion gives the SAME original component inverse equation. -/
theorem inclusion_flanking (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (c : ConnectedComponents (Object K x y q)) : inclusion K x y q (flanking K x y q c) = c := by
  induction c using Quotient.inductionOn' with
  | h T =>
    exact Quotient.sound' (Zigzag.of_hom ((fullInclusion K x y q).app T))

/-- Both SAME original component maps form the genuine original set equivalence. -/
def equivalence (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    ConnectedComponents (Flanked K x y q) ≃ ConnectedComponents (Object K x y q) where
  toFun := inclusion K x y q
  invFun := flanking K x y q
  left_inv := flanking_inclusion K x y q
  right_inv := inclusion_flanking K x y q

/-- The SAME original component set equivalence as the canonical discrete-category equivalence. -/
def discreteEquivalence (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Discrete (ConnectedComponents (Flanked K x y q)) ≌ Discrete (ConnectedComponents (Object K x y q)) :=
  Discrete.equivalence (equivalence K x y q)

/-- The SAME original full-category component-label functor. -/
def projectionFunctor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Object K x y q ⥤ Discrete (ConnectedComponents (Object K x y q)) :=
  ConnectedComponents.functorToDiscrete _ id

/-- The SAME complete original component labels commute with actual original flanking. -/
theorem projectionFunctor_flanking (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    toFlanked K x y q ⋙ Normalization.componentProjectionFunctor K x y q ⋙
      (discreteEquivalence K x y q).functor = projectionFunctor K x y q := by
  refine CategoryTheory.Functor.ext (fun T => ?_) ?_
  · apply Discrete.ext
    exact Quotient.sound' (Zigzag.of_hom ((fullInclusion K x y q).app T))
  · intro T U f
    exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
