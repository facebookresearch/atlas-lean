/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentWeakReflection

/-!
# The original nerve after the original native Bergner replacement

The same original native inclusion is DK weak at every enrichment. Its
full naturality square therefore makes native replacement preserve and
reflect DK weakness on every original functor. Applying the already
proved original nerve recognition at the genuine locally Kan replacements
gives a homotopical functor on the entire original varying-object carrier.

The raw original nerve inclusion has a weak component at a locally Kan
source, retaining the explicit source fibrancy condition.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalCoherentLocalization

open SimplicialEnrichment

/-- The original native replacement reflects as well as preserves the full original DK class. -/
theorem nativeReplacement_map_weak_iff {C D : Carrier.{u}} (F : C ⟶ D) :
    EnrichedDwyerKan.weakEquivalences (OriginalBergnerFibrantReplacement.functor.map F) ↔
      EnrichedDwyerKan.weakEquivalences F := by
  constructor
  · intro h
    let W := EnrichedDwyerKan.weakEquivalences.{u}
    have hComp := W.comp_mem (OriginalBergnerFibrantReplacement.inclusion.app C)
      (OriginalBergnerFibrantReplacement.functor.map F)
      (OriginalBergnerFibrantReplacement.inclusion_original_classes C).2 h
    have hNat := OriginalBergnerFibrantReplacement.inclusion.naturality F
    exact (W.postcomp_iff F (OriginalBergnerFibrantReplacement.inclusion.app D)
      (OriginalBergnerFibrantReplacement.inclusion_original_classes D).2).mp (hNat.symm ▸ hComp)
  · exact OriginalQuillenComparison.nativeReplacement_map_weak F

/-- The same original coherent nerve applied to the same full original native replacement. -/
def nativeReplacedNerve : Carrier.{u} ⥤ SSet.{u} :=
  OriginalBergnerFibrantReplacement.functor.{u} ⋙ coherentNerveFunctor.{u}

/-- Every object of the full native-replaced original nerve is genuinely a quasicategory. -/
theorem nativeReplacedNerve_quasicategory (C : Carrier.{u}) :
    SSet.Quasicategory (nativeReplacedNerve.obj C) :=
  coherentNerve_quasicategory _ (OriginalBergnerFibrantReplacement.homKan C)

/-- The native-replaced original nerve recognizes the original DK class on every original functor. -/
theorem nativeReplacedNerve_map_weak_iff {C D : Carrier.{u}} (F : C ⟶ D) :
    SSet.categoricalEquivalences (nativeReplacedNerve.map F) ↔
      EnrichedDwyerKan.weakEquivalences F :=
  (OriginalQuillenComparison.nerve_weak_iff_original
    (OriginalBergnerFibrantReplacement.functor.map F)
    (OriginalBergnerFibrantReplacement.homKan C)
    (OriginalBergnerFibrantReplacement.homKan D)).trans (nativeReplacement_map_weak_iff F)

/-- The entire original nerve inclusion keeps the actual native inclusion on every original enrichment. -/
def nerveInclusion : coherentNerveFunctor.{u} ⟶ nativeReplacedNerve.{u} :=
  Functor.whiskerRight OriginalBergnerFibrantReplacement.inclusion.{u} coherentNerveFunctor.{u}

/-- Its full simplicial component is the same original coherent nerve map of the native inclusion. -/
theorem nerveInclusion_app (C : Carrier.{u}) :
    nerveInclusion.app C =
      coherentNerveFunctor.map (OriginalBergnerFibrantReplacement.inclusion.app C) := rfl

/-- Every source functor retains the actual original nerve/native-inclusion square. -/
theorem nerveInclusion_naturality {C D : Carrier.{u}} (F : C ⟶ D) :
    coherentNerveFunctor.map F ≫ nerveInclusion.app D =
      nerveInclusion.app C ≫ nativeReplacedNerve.map F :=
  nerveInclusion.naturality F

/-- The raw original nerve/native-replacement inclusion is weak at every genuinely locally Kan source. -/
theorem nerveInclusion_weak (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    SSet.categoricalEquivalences (nerveInclusion.app C) :=
  (OriginalQuillenComparison.nerve_weak_iff_original
    (OriginalBergnerFibrantReplacement.inclusion.app C) hKan
    (OriginalBergnerFibrantReplacement.homKan C)).mpr
      (OriginalBergnerFibrantReplacement.inclusion_original_classes C).2

end CategoryTheory.CoherentRealization.OriginalCoherentLocalization
