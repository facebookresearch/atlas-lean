/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceMappingGadgets
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedGadgetInputs

/-!
# Full original native comma categories of mapping-gadget inputs

The canonical actual pre-equivalence and fully faithful full-subcategory
post-equivalence identify the entire original native comma with the
same full original native pointed inputs into the supplied gadget.
Every actual original native map and complete pointed triangle remains.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

/-- The full original native necklace inputs into the same original full mapping-gadget target. -/
def nativeGadgetInputs (K : OriginalPointed.Category.{u}) :
    CostructuredArrow pointedNativeFunctor K ⥤ CostructuredArrow OriginalPointed.gadgetInclusion K :=
  CostructuredArrow.pre nativeGadgetFunctor OriginalPointed.gadgetInclusion K

/-- The same full original native gadget comma is the entire native pointed input category of the supplied original
gadget. -/
def nativeGadgetCommaEquivalence (K : OriginalPointed.Category.{u})
    (Y : CostructuredArrow OriginalPointed.gadgetInclusion K) :
    CostructuredArrow (nativeGadgetInputs K) Y ≌ CostructuredArrow pointedNativeFunctor Y.left.obj := by
  let _ : OriginalPointed.gadgetInclusion.{u}.Full := inferInstanceAs (ObjectProperty.ι _).Full
  let _ : OriginalPointed.gadgetInclusion.{u}.Faithful := inferInstanceAs (ObjectProperty.ι _).Faithful
  exact (CostructuredArrow.preEquivalence nativeGadgetFunctor Y).trans
    (CostructuredArrow.post nativeGadgetFunctor OriginalPointed.gadgetInclusion Y.left).asEquivalence

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
