/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentNativeReplacedNerve
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Ordinary localization functors from the original coherent adjunction

The original realization preserves categorical weakness on every source,
and the original native-replaced nerve preserves DK weakness on every
varying-object enrichment. Their actual maps therefore descend to the
ordinary localizations at the two original weak classes.

The construction retains the original object and map images exactly.
No equivalence of the underlying categories or isomorphism of the raw
adjunction's unit or counit is assumed.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalCoherentLocalization

open SimplicialEnrichment

/-- The ordinary localization of the original simplicial sets at categorical weakness. -/
abbrev simplicialLocalization := SSet.categoricalEquivalences.{u}.Localization

/-- The ordinary localization of the original varying-object enrichments at DK weakness. -/
abbrev enrichmentLocalization := EnrichedDwyerKan.weakEquivalences.{u}.Localization

/-- The original simplicial localization projection. -/
def simplicialProjection : SSet.{u} ⥤ simplicialLocalization.{u} :=
  SSet.categoricalEquivalences.{u}.Q

/-- The original enrichment localization projection. -/
def enrichmentProjection : Carrier.{u} ⥤ enrichmentLocalization.{u} :=
  EnrichedDwyerKan.weakEquivalences.{u}.Q

/-- Localized original realization inverts every original categorical weak map. -/
theorem realization_inverts : SSet.categoricalEquivalences.{u}.IsInvertedBy
    (realizationFunctor.{u} ⋙ enrichmentProjection.{u}) := by
  intro K L f hf
  exact EnrichedDwyerKan.weakEquivalences.Q_inverts _
    (OriginalQuillenComparison.realizationMap_weak_of_categorical f hf)

/-- Localized original native-replaced nerve inverts every original DK weak functor. -/
theorem nativeReplacedNerve_inverts : EnrichedDwyerKan.weakEquivalences.{u}.IsInvertedBy
    (nativeReplacedNerve.{u} ⋙ simplicialProjection.{u}) := by
  intro C D F hF
  exact SSet.categoricalEquivalences.Q_inverts _
    ((nativeReplacedNerve_map_weak_iff F).mpr hF)

/-- The original realization descended to the ordinary localizations. -/
def left : simplicialLocalization.{u} ⥤ enrichmentLocalization.{u} :=
  Localization.Construction.lift (realizationFunctor ⋙ enrichmentProjection) realization_inverts

/-- The original native-replaced coherent nerve descended to the ordinary localizations. -/
def right : enrichmentLocalization.{u} ⥤ simplicialLocalization.{u} :=
  Localization.Construction.lift (nativeReplacedNerve ⋙ simplicialProjection) nativeReplacedNerve_inverts

/-- The left descent agrees exactly with the original realization followed by projection. -/
theorem left_fac : simplicialProjection.{u} ⋙ left.{u} =
    realizationFunctor.{u} ⋙ enrichmentProjection.{u} :=
  Localization.Construction.fac _ _

/-- The right descent agrees exactly with the original native-replaced nerve followed by projection. -/
theorem right_fac : enrichmentProjection.{u} ⋙ right.{u} =
    nativeReplacedNerve.{u} ⋙ simplicialProjection.{u} :=
  Localization.Construction.fac _ _

/-- The left descent retains the actual original realized object. -/
theorem left_obj_projection (K : SSet.{u}) :
    left.obj (simplicialProjection.obj K) = enrichmentProjection.obj (realization K) := rfl

/-- The right descent retains the actual original nerve of the original native replacement. -/
theorem right_obj_projection (C : Carrier.{u}) :
    right.obj (enrichmentProjection.obj C) = simplicialProjection.obj (nativeReplacedNerve.obj C) := rfl

/-- Every projected source map has the actual original coherent realization as its left image. -/
theorem left_map_projection {K L : SSet.{u}} (f : K ⟶ L) :
    left.map (simplicialProjection.map f) = enrichmentProjection.map (realizationMap f) := by
  have h := Functor.congr_hom left_fac f
  refine h.trans ?_
  change (𝟙 _) ≫ enrichmentProjection.map (realizationMap f) ≫ (𝟙 _) =
    enrichmentProjection.map (realizationMap f)
  simp only [Category.id_comp, Category.comp_id]

/-- Every projected enrichment functor has the actual native-replaced nerve as its right image. -/
theorem right_map_projection {C D : Carrier.{u}} (F : C ⟶ D) :
    right.map (enrichmentProjection.map F) = simplicialProjection.map (nativeReplacedNerve.map F) := by
  have h := Functor.congr_hom right_fac F
  refine h.trans ?_
  change (𝟙 _) ≫ simplicialProjection.map (nativeReplacedNerve.map F) ≫ (𝟙 _) =
    simplicialProjection.map (nativeReplacedNerve.map F)
  simp only [Category.id_comp, Category.comp_id]

end CategoryTheory.CoherentRealization.OriginalCoherentLocalization
