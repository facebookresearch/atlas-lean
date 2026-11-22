/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.StrictReplacement
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.MiddleComparison
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.MappedFactorCompatibility

/-!
# Original literal strict and full D_R source replacement comparisons

The original full middle counit and complete source-zero Arrow comparisons
supply actual Q/R natural isomorphisms. Both original π/ι factor squares retain
the full original data and every actual strict/source map.
The original map and factor statements retain `_B` to quantify over every caller
bottom of the given κ algorithm. The canonical implementation uses the
unique original bottom, and the whole-record readbacks identify it at every `_B`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed ZeroObject

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictReplacement

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

section ActualMiddleCompatibility
variable {W₁ W₂ : MorphismProperty SourceCarrier.{u, v}}
  [W₁.RespectsIso] [W₂.RespectsIso]

private theorem actual_strict_right_compatibility (data : FunctorialFactorizationData W₁ W₂)
    (A : StrictSourceCarrier.{u, v} ⥤ Arrow StrictSourceCarrier.{u, v})
    (A' : SourceCarrier.{u, v} ⥤ Arrow SourceCarrier.{u, v})
    (cA : A ⋙ presentation.functor.mapArrow ≅ presentation.functor ⋙ A')
    (X : StrictSourceCarrier.{u, v}) :
    (originalMiddleComparison presentation.functor data.Z (data.ofEquivalence presentation).Z
      A A' (data.ofEquivalenceZComparisonIso presentation) cA).hom.app X ≫
        data.p.app (A'.obj (presentation.functor.obj X)) =
      presentation.functor.map ((data.ofEquivalence presentation).p.app (A.obj X)) ≫
        (cA.hom.app X).right :=
  originalRightFactorCompatibility presentation.functor data.Z (data.ofEquivalence presentation).Z
    data.p (data.ofEquivalence presentation).p A A'
    (data.ofEquivalenceZComparisonIso presentation) cA
    (data.ofEquivalence_mapped_p presentation) X

private theorem actual_strict_left_compatibility (data : FunctorialFactorizationData W₁ W₂)
    (A : StrictSourceCarrier.{u, v} ⥤ Arrow StrictSourceCarrier.{u, v})
    (A' : SourceCarrier.{u, v} ⥤ Arrow SourceCarrier.{u, v})
    (cA : A ⋙ presentation.functor.mapArrow ≅ presentation.functor ⋙ A')
    (X : StrictSourceCarrier.{u, v}) :
    presentation.functor.map ((data.ofEquivalence presentation).i.app (A.obj X)) ≫
      (originalMiddleComparison presentation.functor data.Z (data.ofEquivalence presentation).Z
        A A' (data.ofEquivalenceZComparisonIso presentation) cA).hom.app X =
          (cA.hom.app X).left ≫ data.i.app (A'.obj (presentation.functor.obj X)) :=
  originalLeftFactorCompatibility presentation.functor data.Z (data.ofEquivalence presentation).Z
    data.i (data.ofEquivalence presentation).i A A'
    (data.ofEquivalenceZComparisonIso presentation) cA
    (data.ofEquivalence_mapped_i presentation) X
end ActualMiddleCompatibility

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]


/-- The complete strict/source Q comparison retains original I data and zero maps. -/
def cofibrantComparisonIso : cofibrantReplacement.{u, v} ⋙ presentation.functor ≅
    presentation.functor ⋙ OriginalReplacement.cofibrantReplacement :=
  originalMiddleComparison presentation.functor originalCofibrantFactorizationData.Z
    strictOriginalCofibrantFactorizationData.Z fromZeroArrow OriginalReplacement.fromZeroArrow
    strictOriginalCofibrantFactorizationDataComparisonIso fromZeroArrowComparisonIso

/-- The complete strict/source R comparison retains original J data and zero maps. -/
def fibrantComparisonIso : fibrantReplacement.{u, v} ⋙ presentation.functor ≅
    presentation.functor ⋙ OriginalReplacement.fibrantReplacement :=
  originalMiddleComparison presentation.functor originalFibrantFactorizationData.Z
    strictOriginalFibrantFactorizationData.Z toZeroArrow OriginalReplacement.toZeroArrow
    strictOriginalFibrantFactorizationDataComparisonIso toZeroArrowComparisonIso

omit B in
/-- The original complete π factor square is the actual supplied middle/zero Arrow comparison. -/
theorem cofibrantComparison_p [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (X : StrictSourceCarrier.{u, v})
  :
    (originalMiddleComparison presentation.functor originalCofibrantFactorizationData.Z
    (originalCofibrantFactorizationData.ofEquivalence presentation).Z fromZeroArrow
    OriginalReplacement.fromZeroArrow
    (originalCofibrantFactorizationData.ofEquivalenceZComparisonIso presentation)
    fromZeroArrowComparisonIso).hom.app X ≫
      originalCofibrantFactorizationData.p.app
        (OriginalReplacement.fromZeroArrow.obj (presentation.functor.obj X)) =
      presentation.functor.map ((originalCofibrantFactorizationData.ofEquivalence
        presentation).p.app
        (fromZeroArrow.obj X)) ≫ (fromZeroArrowComparisonIso.hom.app X).right :=
  actual_strict_right_compatibility (originalCofibrantFactorizationData.{u, v})
    fromZeroArrow OriginalReplacement.fromZeroArrow fromZeroArrowComparisonIso X

omit B in
/-- The original complete ι factor square is the actual supplied middle/zero Arrow comparison. -/
theorem fibrantComparison_i [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (X : StrictSourceCarrier.{u, v}) :
    presentation.functor.map ((originalFibrantFactorizationData.ofEquivalence presentation).i.app
    (toZeroArrow.obj X)) ≫
    (originalMiddleComparison presentation.functor originalFibrantFactorizationData.Z
      (originalFibrantFactorizationData.ofEquivalence presentation).Z toZeroArrow
      OriginalReplacement.toZeroArrow
      (originalFibrantFactorizationData.ofEquivalenceZComparisonIso presentation)
      toZeroArrowComparisonIso).hom.app X =
        (toZeroArrowComparisonIso.hom.app X).left ≫
          originalFibrantFactorizationData.i.app
            (OriginalReplacement.toZeroArrow.obj (presentation.functor.obj X)) :=
  actual_strict_left_compatibility (originalFibrantFactorizationData.{u, v})
    toZeroArrow OriginalReplacement.toZeroArrow toZeroArrowComparisonIso X

end PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictReplacement
