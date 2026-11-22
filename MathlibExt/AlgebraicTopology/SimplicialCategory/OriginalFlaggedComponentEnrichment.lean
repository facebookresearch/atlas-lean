/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentUnit
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentAssociativity
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentCompositionNaturality

/-!
# The genuine original full-component simplicial enrichment

Objects are exactly the original input vertices. Each Hom is the SAME
simplicial set of full original flagged components; the identity and
composition are the original zero necklace and full native concatenation.
All enriched laws follow from actual original full flagged maps.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

/-- Every original scalar operator retains the SAME zero necklace and full singleton coefficient. -/
theorem scalarObject_unit (K : SSet.{u}) (x : K _⦋0⦌) {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    scalarObject θ (unit K q x) = unit K r x := by
  rfl

/-- The actual original component identity in every complete scalar degree. -/
def identity (K : SSet.{u}) (x : K _⦋0⦌) : 𝟙_ SSet.{u} ⟶ simplicialSet K x x where
  app q := ↾fun _ => ConnectedComponents.mk (unit K q x)
  naturality _q _r θ := by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg ConnectedComponents.mk (scalarObject_unit K x θ).symm

/-- The actual full original component simplicial enrichment on the SAME original vertex type. -/
@[instance_reducible]
def enrichment (K : SSet.{u}) : EnrichedCategory SSet.{u} (K _⦋0⦌) where
  Hom := simplicialSet K
  id := identity K
  comp := composition K
  id_comp x y := by
    ext q a
    exact concatenate_unit_left a
  comp_id x y := by
    ext q a
    exact concatenate_unit_right a
  assoc w x y z := by
    ext q abc
    obtain ⟨a, b, c⟩ := abc
    exact concatenate_assoc a b c

/-- Bundle the actual original component enrichment without changing ANY original object labels. -/
def category (K : SSet.{u}) : SimplicialEnrichment.Carrier.{u} := by
  let := enrichment K
  exact SimplicialEnrichment.of (K _⦋0⦌)

/-- The SAME full original component Hom is retained literally by its actual bundle. -/
theorem category_hom (K : SSet.{u}) (x y : K _⦋0⦌) :
    ((show category K from x) ⟶[SSet.{u}] (show category K from y) : SSet.{u}) =
      simplicialSet K x y := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
