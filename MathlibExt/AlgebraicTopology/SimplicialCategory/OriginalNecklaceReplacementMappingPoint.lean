/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedInnerHornReplacement
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingSimplexPoint
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceJoyalInclusion
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.RightMappingBrown
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexQuasicategory

/-!
# Genuine original native replacement right-mapping point comparison

The same native inclusion is inner anodyne. The canonical actual
inner-horn replacement extends that original map into the same ambient
ordinal simplex. Two-out-of-three proves the actual extension categorical
weak; genuine quasicategory right-mapping preservation and the full
original ordinal point iso give the replacement's true point weakness.
-/

noncomputable section

universe u

open CategoryTheory Opposite HomotopicalAlgebra
open scoped Simplicial

attribute [local instance] JoyalSSet.modelCategory

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace OriginalRawRightMapping

/-- The actual original native-to-ambient inclusion extends across its same canonical original replacement unit. -/
def replacementAmbientExtension (T : Data) :
    SSet.innerHornReplacement.obj T.object.{u} ⟶ (Δ[T.dimension] : SSet.{u}) := by
  exact (SSet.exists_innerHornReplacement_extension (complex T.joints).ι).choose

/-- The same original extension retains the literal full native inclusion triangle. -/
theorem replacementAmbientExtension_unit (T : Data) :
    SSet.innerHornReplacementUnit.app T.object.{u} ≫ replacementAmbientExtension T = (complex T.joints).ι := by
  exact (SSet.exists_innerHornReplacement_extension (complex T.joints).ι).choose_spec.1

/-- The same actual original extension is genuinely categorical weak by the two original inner-anodyne maps. -/
theorem replacementAmbientExtension_categorical (T : Data) :
    SSet.categoricalEquivalences (replacementAmbientExtension.{u} T) :=
  SSet.categoricalEquivalences.of_precomp (SSet.innerHornReplacementUnit.app T.object) _
    (SSet.innerHornReplacementUnit_categorical T.object)
    ((replacementAmbientExtension_unit T).symm ▸ inclusion_categoricalEquivalence T)

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
