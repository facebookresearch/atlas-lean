/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklacePointedInputEquivalence

/-!
# The full original native comma input comparison

The canonical costructured-arrow pre-equivalence gives the original
native input category over every pointed carrier. Both whole original
map directions and the complete native objects are retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

/-- The same full original native-to-pointed-input functor at the supplied original target. -/
def nativeIntoPointedInputs (K : OriginalPointed.Category.{u}) :
    CostructuredArrow pointedNativeFunctor K ⥤ CostructuredArrow (𝟭 OriginalPointed.Category.{u}) K :=
  CostructuredArrow.pre pointedNativeFunctor (𝟭 OriginalPointed.Category.{u}) K

/-- The canonical full original native comma category is the same entire native input category of its target carrier. -/
def nativeCommaEquivalence (K : OriginalPointed.Category.{u})
    (Y : CostructuredArrow (𝟭 OriginalPointed.Category.{u}) K) :
    CostructuredArrow (nativeIntoPointedInputs K) Y ≌ CostructuredArrow pointedNativeFunctor Y.left :=
  CostructuredArrow.preEquivalence pointedNativeFunctor Y

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
