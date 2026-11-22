/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.StrictLevelHo
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.StrictSourceComparison
import MathlibExt.CategoryTheory.Localization.OriginalBifibrantComparison

/-!
# Full original D_R strict/source Ho replacement comparison maps

Each actual strict/source Q/R middle and zero Arrow comparison lifts through
the real quotient functors. All four projected hom and inverse components
remain the original full source images of the original raw comparisons.
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

/-- The complete original cofibrant strict/source Ho comparison retains the same given data. -/
def cofibrantComparisonIso :
    OriginalStrictReplacement.cofibrantReplacementHo.{u, v} ⋙ equivalence.functor ≅
      equivalence.functor ⋙ OriginalReplacement.cofibrantReplacementHo :=
  Localization.originalLocalizedComparison
    OriginalStrictReplacement.sourceWeak OriginalReplacement.sourceWeak
    OriginalStrictReplacement.cofibrantReplacement OriginalReplacement.cofibrantReplacement
    OriginalStrictReplacement.presentation.functor OriginalStrictReplacement.cofibrant_inverts
    OriginalReplacement.cofibrant_inverts restriction_inverts
    OriginalStrictReplacement.cofibrantComparisonIso

/-- The entire original cofibrant hom component is the literal projected full source map. -/
theorem cofibrantComparisonIso_hom_projected (X : StrictSourceCarrier.{u, v}) :
    cofibrantComparisonIso.hom.app (OriginalStrictReplacement.projection.obj X) =
      OriginalReplacement.projection.map
        (OriginalStrictReplacement.cofibrantComparisonIso.hom.app X) :=
  Localization.originalLocalizedComparison_hom_projected
    OriginalStrictReplacement.sourceWeak OriginalReplacement.sourceWeak
    OriginalStrictReplacement.cofibrantReplacement OriginalReplacement.cofibrantReplacement
    OriginalStrictReplacement.presentation.functor OriginalStrictReplacement.cofibrant_inverts
    OriginalReplacement.cofibrant_inverts restriction_inverts
    OriginalStrictReplacement.cofibrantComparisonIso X

/-- The entire original cofibrant inv component is the literal projected full source map. -/
theorem cofibrantComparisonIso_inv_projected (X : StrictSourceCarrier.{u, v}) :
    cofibrantComparisonIso.inv.app (OriginalStrictReplacement.projection.obj X) =
      OriginalReplacement.projection.map
        (OriginalStrictReplacement.cofibrantComparisonIso.inv.app X) :=
  Localization.originalLocalizedComparison_inv_projected
    OriginalStrictReplacement.sourceWeak OriginalReplacement.sourceWeak
    OriginalStrictReplacement.cofibrantReplacement OriginalReplacement.cofibrantReplacement
    OriginalStrictReplacement.presentation.functor OriginalStrictReplacement.cofibrant_inverts
    OriginalReplacement.cofibrant_inverts restriction_inverts
    OriginalStrictReplacement.cofibrantComparisonIso X

/-- The complete original fibrant strict/source Ho comparison retains the same given data. -/
def fibrantComparisonIso :
    OriginalStrictReplacement.fibrantReplacementHo.{u, v} ⋙ equivalence.functor ≅
      equivalence.functor ⋙ OriginalReplacement.fibrantReplacementHo :=
  Localization.originalLocalizedComparison
    OriginalStrictReplacement.sourceWeak OriginalReplacement.sourceWeak
    OriginalStrictReplacement.fibrantReplacement OriginalReplacement.fibrantReplacement
    OriginalStrictReplacement.presentation.functor OriginalStrictReplacement.fibrant_inverts
    OriginalReplacement.fibrant_inverts restriction_inverts
    OriginalStrictReplacement.fibrantComparisonIso

/-- The entire original fibrant hom component is the literal projected full source map. -/
theorem fibrantComparisonIso_hom_projected (X : StrictSourceCarrier.{u, v}) :
    fibrantComparisonIso.hom.app (OriginalStrictReplacement.projection.obj X) =
      OriginalReplacement.projection.map
        (OriginalStrictReplacement.fibrantComparisonIso.hom.app X) :=
  Localization.originalLocalizedComparison_hom_projected
    OriginalStrictReplacement.sourceWeak OriginalReplacement.sourceWeak
    OriginalStrictReplacement.fibrantReplacement OriginalReplacement.fibrantReplacement
    OriginalStrictReplacement.presentation.functor OriginalStrictReplacement.fibrant_inverts
    OriginalReplacement.fibrant_inverts restriction_inverts
    OriginalStrictReplacement.fibrantComparisonIso X

/-- The entire original fibrant inv component is the literal projected full source map. -/
theorem fibrantComparisonIso_inv_projected (X : StrictSourceCarrier.{u, v}) :
    fibrantComparisonIso.inv.app (OriginalStrictReplacement.projection.obj X) =
      OriginalReplacement.projection.map
        (OriginalStrictReplacement.fibrantComparisonIso.inv.app X) :=
  Localization.originalLocalizedComparison_inv_projected
    OriginalStrictReplacement.sourceWeak OriginalReplacement.sourceWeak
    OriginalStrictReplacement.fibrantReplacement OriginalReplacement.fibrantReplacement
    OriginalStrictReplacement.presentation.functor OriginalStrictReplacement.fibrant_inverts
    OriginalReplacement.fibrant_inverts restriction_inverts
    OriginalStrictReplacement.fibrantComparisonIso X

end PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictLevelHo
