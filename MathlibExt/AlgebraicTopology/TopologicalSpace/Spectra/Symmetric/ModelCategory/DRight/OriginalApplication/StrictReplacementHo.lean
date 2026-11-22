/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.StrictReplacementProperties
import Mathlib.CategoryTheory.Localization.Construction

/-!
# Literal original D_R source level Ho outputs for the SAME OLD-J data

The actual returned D_R source model gives the original level weak class.
The same original data π/ι squares prove weak preservation, then the actual
localization construction lifts both complete original functors and maps.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed ZeroObject

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictReplacement

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The exact original D_R source weak class comes from the actual returned source model. -/
abbrev sourceWeak : MorphismProperty StrictSourceCarrier.{u, v} :=
  BasedNativePresentation.strictModelCategory.categoryWithWeakEquivalences.weakEquivalences

private theorem sourceWeak_comp : sourceWeak.{u, v}.IsStableUnderComposition := by
  let _ : ModelCategory StrictSourceCarrier.{u, v} := BasedNativePresentation.strictModelCategory
  change (weakEquivalences StrictSourceCarrier.{u, v}).IsStableUnderComposition
  infer_instance

private theorem sourceWeak_pre : sourceWeak.{u, v}.HasOfPrecompProperty sourceWeak.{u, v} := by
  let _ : ModelCategory StrictSourceCarrier.{u, v} := BasedNativePresentation.strictModelCategory
  change (weakEquivalences StrictSourceCarrier.{u, v}).HasOfPrecompProperty
    (weakEquivalences StrictSourceCarrier.{u, v})
  infer_instance

private theorem sourceWeak_post : sourceWeak.{u, v}.HasOfPostcompProperty sourceWeak.{u, v} := by
  let _ : ModelCategory StrictSourceCarrier.{u, v} := BasedNativePresentation.strictModelCategory
  change (weakEquivalences StrictSourceCarrier.{u, v}).HasOfPostcompProperty
    (weakEquivalences StrictSourceCarrier.{u, v})
  infer_instance

attribute [local instance] sourceWeak_comp sourceWeak_pre sourceWeak_post

private theorem pi_mem_sourceWeak (X : StrictSourceCarrier.{u, v}) :
    sourceWeak (cofibrantProjection.app X) :=
  (strictOriginalCofibrantFactorizationData_classes (fromZeroArrow.obj X)).2.2

private theorem iota_mem_sourceWeak (X : StrictSourceCarrier.{u, v}) :
    sourceWeak (fibrantUnit.app X) :=
  (strictOriginalFibrantFactorizationData_classes (toZeroArrow.obj X)).1.2

/-- The SAME original source Q preserves every actual original source weak map. -/
theorem cofibrantReplacement_map_weak {X Y : StrictSourceCarrier.{u, v}} (f : X ⟶ Y)
    (hf : sourceWeak f) : sourceWeak (cofibrantReplacement.map f) := by
  apply sourceWeak.of_postcomp (cofibrantReplacement.map f) (cofibrantProjection.app Y)
    (pi_mem_sourceWeak Y)
  rw [cofibrantProjection_naturality]
  exact sourceWeak.comp_mem _ _ (pi_mem_sourceWeak X) hf

/-- The SAME original source R preserves every actual original source weak map. -/
theorem fibrantReplacement_map_weak {X Y : StrictSourceCarrier.{u, v}} (f : X ⟶ Y)
    (hf : sourceWeak f) : sourceWeak (fibrantReplacement.map f) := by
  apply sourceWeak.of_precomp (fibrantUnit.app X) (fibrantReplacement.map f)
    (iota_mem_sourceWeak X)
  rw [← fibrantUnit_naturality]
  exact sourceWeak.comp_mem _ _ hf (iota_mem_sourceWeak Y)

/-- The actual original source quotient category. -/
abbrev HoCategory := sourceWeak.{u, v}.Localization

/-- The literal original D_R source quotient projection. -/
abbrev projection : StrictSourceCarrier.{u, v} ⥤ HoCategory.{u, v} := sourceWeak.Q

/-- The original full Q followed by actual source projection inverts the original weak class. -/
theorem cofibrant_inverts : sourceWeak.{u, v}.IsInvertedBy (cofibrantReplacement ⋙ projection) :=
  fun _ _ f hf => Localization.inverts projection sourceWeak (cofibrantReplacement.map f)
    (cofibrantReplacement_map_weak f hf)

/-- The original full R followed by actual source projection inverts the original weak class. -/
theorem fibrant_inverts : sourceWeak.{u, v}.IsInvertedBy (fibrantReplacement ⋙ projection) :=
  fun _ _ f hf => Localization.inverts projection sourceWeak (fibrantReplacement.map f)
    (fibrantReplacement_map_weak f hf)

/-- The actual source Q Ho action retains the full OLD-J data and all original maps. -/
def cofibrantReplacementHo : HoCategory.{u, v} ⥤ HoCategory.{u, v} :=
  Localization.Construction.lift (cofibrantReplacement ⋙ projection) cofibrant_inverts

/-- The actual source R Ho action retains the full OLD-J data and all original maps. -/
def fibrantReplacementHo : HoCategory.{u, v} ⥤ HoCategory.{u, v} :=
  Localization.Construction.lift (fibrantReplacement ⋙ projection) fibrant_inverts

/-- The entire original Q Ho projection is strictly the same raw functor and quotient. -/
theorem cofibrantReplacementHo_projection :
    projection.{u, v} ⋙ cofibrantReplacementHo = cofibrantReplacement ⋙ projection :=
  Localization.Construction.fac _ _

/-- The entire original R Ho projection is strictly the same raw functor and quotient. -/
theorem fibrantReplacementHo_projection :
    projection.{u, v} ⋙ fibrantReplacementHo = fibrantReplacement ⋙ projection :=
  Localization.Construction.fac _ _

/-- Every projected original Q map retains the complete same OLD-J source I middle map. -/
theorem cofibrantReplacementHo_map_projected {X Y : StrictSourceCarrier.{u, v}} (f : X ⟶ Y) :
    cofibrantReplacementHo.map (projection.map f) =
      projection.map (cofibrantReplacement.map f) :=
  Functor.congr_hom cofibrantReplacementHo_projection f

/-- Every projected original R map retains the complete same OLD-J source J middle map. -/
theorem fibrantReplacementHo_map_projected {X Y : StrictSourceCarrier.{u, v}} (f : X ⟶ Y) :
    fibrantReplacementHo.map (projection.map f) = projection.map (fibrantReplacement.map f) :=
  Functor.congr_hom fibrantReplacementHo_projection f

end PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictReplacement
