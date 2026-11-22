/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentDerivedUnit

/-!
# The SAME original realization recognizes every categorical weak map

The actual original weak natural replacement unit identifies the
entire original source map with its original replaced-nerve map.
The genuine native inclusion and nerve reflection between fibrant
enrichments then give recognition for EVERY original simplicial map.
No source quasicategory or raw realization Kan premise is used.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison

open SimplicialEnrichment

/-- The SAME original realization and the SAME native replaced realization have exactly the same original DK weak-map
class. -/
theorem replacedRealization_weak_iff {K L : SSet.{u}} (f : K ⟶ L) :
    EnrichedDwyerKan.weakEquivalences (replacedRealization.map f) ↔
      EnrichedDwyerKan.weakEquivalences (realizationMap f) := by
  let W := EnrichedDwyerKan.weakEquivalences.{u}
  have hNat : realizationMap f ≫ OriginalBergnerFibrantReplacement.inclusion.app (realization L) =
      OriginalBergnerFibrantReplacement.inclusion.app (realization K) ≫ replacedRealization.map f :=
    OriginalBergnerFibrantReplacement.inclusion.naturality (realizationMap f)
  exact (W.precomp_iff _ _ (OriginalBergnerFibrantReplacement.inclusion_original_classes (realization K)).2).symm.trans
    ((Iff.of_eq (congrArg (fun g : realization K ⟶ replacedRealization.obj L => W g) hNat.symm)).trans
      (W.postcomp_iff _ _ (OriginalBergnerFibrantReplacement.inclusion_original_classes (realization L)).2))

/-- The SAME original coherent realization recognizes categorical weakness of EVERY original simplicial map, with no
source quasicategory or raw Hom Kan assumption. -/
theorem realizationMap_weak_iff {K L : SSet.{u}} (f : K ⟶ L) :
    EnrichedDwyerKan.weakEquivalences (realizationMap f) ↔ SSet.categoricalEquivalences f := by
  let W := SSet.categoricalEquivalences.{u}
  have hNat := replacementUnit_naturality f
  have hRight : SSet.categoricalEquivalences (coherentNerveFunctor.map (replacedRealization.map f)) ↔
      EnrichedDwyerKan.weakEquivalences (replacedRealization.map f) :=
    nerve_weak_iff_original _ (OriginalBergnerFibrantReplacement.homKan (realization K))
      (OriginalBergnerFibrantReplacement.homKan (realization L))
  have hSource : W f ↔ W (coherentNerveFunctor.map (replacedRealization.map f)) :=
    (W.postcomp_iff _ _ (replacementUnit_weak L)).symm.trans
      ((Iff.of_eq (congrArg (fun g : K ⟶ coherentNerveFunctor.obj (replacedRealization.obj L) => W g) hNat)).trans
        (W.precomp_iff _ _ (replacementUnit_weak K)))
  exact ((hSource.trans hRight).trans (replacedRealization_weak_iff f)).symm

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
