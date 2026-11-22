/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceReplacementRightPoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHomFunctor

/-!
# Original pointed inputs categorically equivalent to an ordinal simplex

A genuine source map to a standard simplex, weak in the actual Joyal
class and retaining its two endpoints, is legitimate geometric input.
Its actual canonical replacement extension stays categorical weak.
No original raw mapping comparison weakness is assumed by this source
predicate.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- Legitimate original source data of a pointed ordinal comparison, retaining its entire map and both original
endpoints. -/
structure OrdinalComparison (X : Category.{u}) where
  /-- The original target ordinal dimension. -/
  dimension : ℕ
  /-- The actual full source simplicial map. -/
  map : X.right ⟶ (Δ[dimension] : SSet.{u})
  /-- The actual original source map lies in the genuine categorical weak class. -/
  categorical : SSet.categoricalEquivalences map
  /-- The same original initial endpoint. -/
  source : source X ≫ map = OriginalRawRightMapping.simplexVertex dimension 0
  /-- The same original terminal endpoint. -/
  target : target X ≫ map = OriginalRawRightMapping.simplexVertex dimension (Fin.last dimension)

/-- The actual canonical replacement extension of the original complete ordinal-comparison map. -/
def ordinalComparisonExtension (X : Category.{u}) (h : OrdinalComparison X) :
    (replacementFunctor.obj X).right ⟶ (Δ[h.dimension] : SSet.{u}) := by
  exact (SSet.exists_innerHornReplacement_extension h.map).choose

/-- The same full original extension retains its actual original unit triangle. -/
theorem ordinalComparisonExtension_unit (X : Category.{u}) (h : OrdinalComparison X) :
    (replacementUnit.app X).right ≫ ordinalComparisonExtension X h = h.map := by
  exact (SSet.exists_innerHornReplacement_extension h.map).choose_spec.1

/-- The same actual original replacement extension is categorical weak by the two original source maps. -/
theorem ordinalComparisonExtension_categorical (X : Category.{u}) (h : OrdinalComparison X) :
    SSet.categoricalEquivalences (ordinalComparisonExtension X h) :=
  SSet.categoricalEquivalences.of_precomp (replacementUnit.app X).right _
    (replacementUnit_categorical X) ((ordinalComparisonExtension_unit X h).symm ▸ h.categorical)

end CategoryTheory.CoherentRealization.OriginalPointed
