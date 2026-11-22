/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.Replacement
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.StrictSource
import MathlibExt.CategoryTheory.Limits.Shapes.ZeroObjectArrowFunctors

/-!
# Literal strict original D_R source carrier and source Ho comparisons

The actual strict source completion equivalence retains the original zero
and every full D_R source morphism. The literal original I/J algorithms map
through restriction/extension with original unit/counit and all source maps.
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

/-- The actual full literal strict/source given equivalence. -/
abbrev presentation : StrictSourceCarrier.{u, v} ≌ SourceCarrier.{u, v} :=
  BasedNativePresentation.strictEquivalence (A := PointedCGWH.SymmetricDRight.Index)

/-- The actual literal strict zero is the original source zero through the given inverse. -/
abbrev zero : StrictSourceCarrier.{u, v} :=
  presentation.inverse.obj OriginalReplacement.zero

omit B in
/-- The genuine chosen strict zero is initial and terminal through the actual equivalence. -/
theorem zero_isZero : IsZero zero.{u, v} :=
  IsZero.of_full_of_faithful_of_isZero presentation.functor zero
    (OriginalReplacement.zero_isZero.of_iso
      (presentation.counitIso.app OriginalReplacement.zero))

/-- The complete literal strict initial Arrow functor retains every original map. -/
abbrev fromZeroArrow : StrictSourceCarrier.{u, v} ⥤ Arrow StrictSourceCarrier.{u, v} :=
  originalInitialArrowFunctor zero_isZero

/-- The complete literal strict terminal Arrow functor retains every original map. -/
abbrev toZeroArrow : StrictSourceCarrier.{u, v} ⥤ Arrow StrictSourceCarrier.{u, v} :=
  originalTerminalArrowFunctor zero_isZero

/-- The same original literal strict I data constructs the actual Q middle functor. -/
def cofibrantReplacement : StrictSourceCarrier.{u, v} ⥤ StrictSourceCarrier.{u, v} :=
  fromZeroArrow ⋙ strictOriginalCofibrantFactorizationData.Z

/-- The same original literal strict J data constructs the actual R middle functor. -/
def fibrantReplacement : StrictSourceCarrier.{u, v} ⥤ StrictSourceCarrier.{u, v} :=
  toZeroArrow ⋙ strictOriginalFibrantFactorizationData.Z

/-- The original strict π is exactly the old transported I second factor. -/
def cofibrantProjection : cofibrantReplacement.{u, v} ⟶ 𝟭 StrictSourceCarrier.{u, v} :=
  Functor.whiskerLeft fromZeroArrow strictOriginalCofibrantFactorizationData.p

/-- The original strict ι is exactly the old transported J first factor. -/
def fibrantUnit : 𝟭 StrictSourceCarrier.{u, v} ⟶ fibrantReplacement.{u, v} :=
  Functor.whiskerLeft toZeroArrow strictOriginalFibrantFactorizationData.i

/-- The original source counit supplies both full literal strict zero Arrow comparisons. -/
def zeroComparisonIso : presentation.functor.obj zero.{u, v} ≅ OriginalReplacement.zero :=
  presentation.counitIso.app OriginalReplacement.zero

/-- All full literal strict source initial Arrow maps use the exact given zero counit. -/
def fromZeroArrowComparisonIso :
    fromZeroArrow.{u, v} ⋙ presentation.functor.mapArrow ≅
      presentation.functor ⋙ OriginalReplacement.fromZeroArrow :=
  originalInitialArrowFunctorIso presentation.functor zero_isZero
    OriginalReplacement.zero_isZero zeroComparisonIso

/-- All full literal strict source terminal Arrow maps use the same exact given zero counit. -/
def toZeroArrowComparisonIso :
    toZeroArrow.{u, v} ⋙ presentation.functor.mapArrow ≅
      presentation.functor ⋙ OriginalReplacement.toZeroArrow :=
  originalTerminalArrowFunctorIso presentation.functor zero_isZero
    OriginalReplacement.zero_isZero zeroComparisonIso

end PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictReplacement
