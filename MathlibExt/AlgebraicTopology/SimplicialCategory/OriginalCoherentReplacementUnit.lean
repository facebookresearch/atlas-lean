/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerFibrantReplacement
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentQuillenPreservation

/-!
# Actual original coherent replacement unit

The SAME original coherent unit is followed by the SAME original
native Bergner fibrant-replacement inclusion. This is a genuine
natural transformation with its literal original factorization.
Its desired categorical weakness is not assumed or asserted.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison
open SimplicialEnrichment
attribute [local instance] JoyalSSet.modelCategory Bergner.modelCategory

/-- The SAME original native Bergner fibrant replacement preserves actual original DK weak arrows. -/
theorem nativeReplacement_map_weak {C D : Carrier.{u}} (F : C ⟶ D)
    (hF : EnrichedDwyerKan.weakEquivalences F) :
    EnrichedDwyerKan.weakEquivalences (OriginalBergnerFibrantReplacement.functor.map F) := by
  let W := EnrichedDwyerKan.weakEquivalences.{u}
  have h := W.comp_mem F (OriginalBergnerFibrantReplacement.inclusion.app D) hF
    (OriginalBergnerFibrantReplacement.inclusion_original_classes D).2
  have hNat : F ≫ OriginalBergnerFibrantReplacement.inclusion.app D =
      OriginalBergnerFibrantReplacement.inclusion.app C ≫
        OriginalBergnerFibrantReplacement.functor.map F :=
    OriginalBergnerFibrantReplacement.inclusion.naturality F
  exact (W.precomp_iff _ _ (OriginalBergnerFibrantReplacement.inclusion_original_classes C).2).mp
    (hNat ▸ h)

/-- The whole original coherent realization followed by its SAME native original fibrant replacement. -/
def replacedRealization : SSet.{u} ⥤ Carrier.{u} :=
  realizationFunctor.{u} ⋙ OriginalBergnerFibrantReplacement.functor.{u}

/-- The entire original derived-unit comparison formed from the actual original unit and original native replacement
inclusion. -/
def replacementUnit :
    𝟭 SSet.{u} ⟶ replacedRealization.{u} ⋙ coherentNerveFunctor.{u} :=
  unitNatTrans.{u} ≫
    Functor.whiskerLeft realizationFunctor.{u}
      (Functor.whiskerRight OriginalBergnerFibrantReplacement.inclusion.{u} coherentNerveFunctor.{u})

/-- The SAME replacement unit has precisely its two original full simplicial factors. -/
theorem replacementUnit_app (K : SSet.{u}) :
    replacementUnit.app K = unit K ≫ coherentNerveFunctor.map
      (OriginalBergnerFibrantReplacement.inclusion.app (realization K)) := rfl

/-- The genuine natural replacement unit keeps every original source-map square. -/
theorem replacementUnit_naturality {K L : SSet.{u}} (f : K ⟶ L) :
    f ≫ replacementUnit.app L =
      replacementUnit.app K ≫ coherentNerveFunctor.map
        (OriginalBergnerFibrantReplacement.functor.map (realizationFunctor.map f)) :=
  replacementUnit.naturality f

/-- The SAME original replaced realization target is genuinely fibrant, for every original simplicial set. -/
theorem replacedRealization_isFibrant (K : SSet.{u}) :
    IsFibrant (replacedRealization.obj K) :=
  OriginalBergnerFibrantReplacement.isFibrant (realization K)

/-- Its SAME original full coherent nerve is therefore a quasicategory with every original coefficient retained. -/
theorem replacementUnit_target_quasicategory (K : SSet.{u}) :
    SSet.Quasicategory (coherentNerveFunctor.obj (replacedRealization.obj K)) :=
  coherentNerve_quasicategory _ (OriginalBergnerFibrantReplacement.homKan (realization K))

/-- Every original categorical weak arrow is preserved by the actual original replaced realization. -/
theorem replacedRealization_map_weak {K L : SSet.{u}} (f : K ⟶ L)
    (hf : SSet.categoricalEquivalences f) :
    EnrichedDwyerKan.weakEquivalences (replacedRealization.map f) :=
  nativeReplacement_map_weak _ (realizationMap_weak_of_categorical f hf)

/-- The SAME original replacement-unit target functor preserves actual original categorical weak arrows. -/
theorem replacementUnit_target_map_weak {K L : SSet.{u}} (f : K ⟶ L)
    (hf : SSet.categoricalEquivalences f) :
    SSet.categoricalEquivalences
      (coherentNerveFunctor.map (replacedRealization.map f)) :=
  (nerve_weak_iff_original _
    (OriginalBergnerFibrantReplacement.homKan (realization K))
    (OriginalBergnerFibrantReplacement.homKan (realization L))).mpr
      (replacedRealization_map_weak f hf)

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
