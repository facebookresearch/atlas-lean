/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentMappingWeakReflection
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentAdjunctEssentialSurjectivity
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentCounitWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentQuillenPreservation
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKanRecognition

/-!
# The actual original coherent adjunct weak-map criterion

For every original quasicategory source and locally Kan enriched
target, an actual counit factorization gives the weak-map criterion
for the SAME two original maps. Mapping weakness comes from the proved
original raw comparison and its source-naturality square. Essential
surjectivity follows the same original vertex and counit object maps.
Neither raw realization is assumed locally Kan.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison

open SimplicialEnrichment

/-- The SAME actual original coherent counit factorization recognizes categorical weakness of the whole original adjunct
exactly by DK weakness of the original enriched map. -/
theorem originalAdjunct_weak_iff {K : SSet.{u}} [SSet.Quasicategory K] {C : Carrier.{u}}
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (g : K ⟶ coherentNerveFunctor.obj C) (F : realization K ⟶ C)
    (hfac : realizationMap g ≫ counit C = F) :
    EnrichedDwyerKan.weakEquivalences F ↔ SSet.categoricalEquivalences g := by
  let _ : SSet.Quasicategory (coherentNerveFunctor.obj C) := coherentNerve_quasicategory C hKan
  have hCounit := counit_DKweak C hKan
  constructor
  · intro hF
    have hReal : EnrichedDwyerKan.weakEquivalences (realizationMap g) :=
      EnrichedDwyerKan.weak_of_postcomp _ _ hCounit (hfac.symm ▸ hF)
    exact SSet.isDwyerKanEquivalence.categoricalEquivalences
      ⟨adjunct_essSurj_of_component hKan g F hfac hF.2,
        rightMappingMap_weak_of_realizationLocalWeak g hReal.1⟩
  · intro hg
    exact hfac ▸ EnrichedDwyerKan.comp_weak _ _
      (realizationMap_weak_of_categorical g hg) hCounit

/-- The SAME original coherent Hom equivalence satisfies the genuine weak-map criterion on every quasicategory and
locally Kan target. -/
theorem coherentHomEquiv_weak_iff (K : SSet.{u}) [SSet.Quasicategory K] (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (F : realization K ⟶ C) :
    EnrichedDwyerKan.weakEquivalences F ↔
      SSet.categoricalEquivalences (coherentHomEquiv K C F) := by
  apply originalAdjunct_weak_iff hKan (coherentHomEquiv K C F) F
  exact (realizationAdjunction.homEquiv_counit (g := coherentHomEquiv K C F)).symm.trans
    ((coherentHomEquiv K C).symm_apply_apply F)

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
