/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.StrictReplacementHo
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.ReplacementHo
import MathlibExt.CategoryTheory.Localization.OriginalEquivalence

/-!
# Literal strict and full original D_R source level Ho equivalence

The actual restriction and extension transport their real returned weak
classes. The full supplied equivalence lifts with both original quotient
projections and original unit/counit, with no source-model dictionary input.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed ZeroObject

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictLevelHo

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private theorem sourceWeak_respectsIso : OriginalReplacement.sourceWeak.{u, v}.RespectsIso := by
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  change (weakEquivalences SourceCarrier.{u, v}).RespectsIso
  infer_instance

attribute [local instance] sourceWeak_respectsIso

/-- The full literal strict restriction is weak-preserving in the actual constructed models. -/
theorem restriction_map_weak {X Y : StrictSourceCarrier.{u, v}} (f : X ⟶ Y)
    (hf : OriginalStrictReplacement.sourceWeak f) :
    OriginalReplacement.sourceWeak (OriginalStrictReplacement.presentation.functor.map f) := hf

/-- The actual given strict extension is weak-preserving through the original source counit. -/
theorem extension_map_weak {X Y : SourceCarrier.{u, v}} (f : X ⟶ Y)
    (hf : OriginalReplacement.sourceWeak f) :
    OriginalStrictReplacement.sourceWeak (OriginalStrictReplacement.presentation.inverse.map f) :=
  (OriginalReplacement.sourceWeak.arrow_mk_iso_iff
    (Arrow.isoOfNatIso OriginalStrictReplacement.presentation.counitIso (Arrow.mk f))).mpr hf

/-- The complete restriction followed by actual source projection inverts every strict weak map. -/
theorem restriction_inverts : OriginalStrictReplacement.sourceWeak.{u, v}.IsInvertedBy
    (OriginalStrictReplacement.presentation.functor ⋙ OriginalReplacement.projection) :=
  fun _ _ f hf => Localization.inverts OriginalReplacement.projection
    OriginalReplacement.sourceWeak _ (restriction_map_weak f hf)

/-- The complete extension followed by actual strict projection inverts every source weak map. -/
theorem extension_inverts : OriginalReplacement.sourceWeak.{u, v}.IsInvertedBy
    (OriginalStrictReplacement.presentation.inverse ⋙ OriginalStrictReplacement.projection) :=
  fun _ _ f hf => Localization.inverts OriginalStrictReplacement.projection
    OriginalStrictReplacement.sourceWeak _ (extension_map_weak f hf)

/-- The complete actual strict/source Ho equivalence retains its given inverse, unit and counit. -/
def equivalence : OriginalStrictReplacement.HoCategory.{u, v} ≌
    OriginalReplacement.HoCategory.{u, v} :=
  Localization.originalEquivalence OriginalStrictReplacement.presentation
    OriginalStrictReplacement.sourceWeak OriginalReplacement.sourceWeak
    restriction_inverts extension_inverts

/-- The entire original strict projection keeps every original restriction object and map. -/
theorem restriction_projection :
    OriginalStrictReplacement.projection.{u, v} ⋙ equivalence.functor =
      OriginalStrictReplacement.presentation.functor ⋙ OriginalReplacement.projection :=
  Localization.originalForward_projection OriginalStrictReplacement.presentation
    OriginalStrictReplacement.sourceWeak OriginalReplacement.sourceWeak restriction_inverts

/-- The entire original source projection keeps every actual extension object and map. -/
theorem extension_projection :
    OriginalReplacement.projection.{u, v} ⋙ equivalence.inverse =
      OriginalStrictReplacement.presentation.inverse ⋙ OriginalStrictReplacement.projection :=
  Localization.originalInverse_projection OriginalStrictReplacement.presentation
    OriginalStrictReplacement.sourceWeak OriginalReplacement.sourceWeak extension_inverts

/-- The actual whole strict/source forward triangle uses the same projected source maps. -/
theorem forward_triangle : Functor.whiskerRight equivalence.unitIso.hom equivalence.functor ≫
    Functor.whiskerLeft equivalence.functor equivalence.counitIso.hom = 𝟙 equivalence.functor := by
  ext X
  exact equivalence.functor_unit_comp X

/-- The actual whole source/strict inverse triangle uses the same given unit and counit maps. -/
theorem inverse_triangle : Functor.whiskerLeft equivalence.inverse equivalence.unitIso.hom ≫
    Functor.whiskerRight equivalence.counitIso.hom equivalence.inverse = 𝟙 equivalence.inverse := by
  ext X
  exact equivalence.unit_inverse_comp X

end PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictLevelHo
