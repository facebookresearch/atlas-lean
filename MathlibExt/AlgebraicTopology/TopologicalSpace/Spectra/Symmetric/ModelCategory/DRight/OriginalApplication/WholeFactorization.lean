/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalFactorization
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.Strict.Factorization
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeEquivalence
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeComposition

/-!
# Complete original OLD-J cardinal factorization diagrams on the genuine D_R source

The actual named D_R data use the original canonical-J module algorithm through
the given source inverse. Source and literal strict entire diagrams retain
original Z/i/p, every caller Arrow map and exact fac; source-index SOA choices
are separate and no algorithm equality is supplied as a premise.
The original map and factor statements retain `_B` to quantify over every caller
bottom of the given κ algorithm. The canonical implementation uses the
unique original bottom, and the whole-record readbacks identify it at every `_B`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open CategoryTheory.MorphismProperty.FunctorialFactorizationData
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed ZeroObject

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalWholeData

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The whole original source I data factor every actual source Arrow with all original maps. -/
abbrev sourceI : Arrow SourceCarrier.{u, v} ⥤ ComposableArrows SourceCarrier.{u, v} 2 :=
  originalCofibrantFactorizationData.originalFactorizationFunctor

/-- The whole original source J data factor every actual source Arrow with all original maps. -/
abbrev sourceJ : Arrow SourceCarrier.{u, v} ⥤ ComposableArrows SourceCarrier.{u, v} 2 :=
  originalFibrantFactorizationData.originalFactorizationFunctor

/-- The whole literal strict I data retain the SAME original transported module algorithm. -/
abbrev strictI : Arrow StrictSourceCarrier.{u, v} ⥤
    ComposableArrows StrictSourceCarrier.{u, v} 2 :=
  strictOriginalCofibrantFactorizationData.originalFactorizationFunctor

/-- The whole literal strict J data retain the SAME original transported module algorithm. -/
abbrev strictJ : Arrow StrictSourceCarrier.{u, v} ⥤
    ComposableArrows StrictSourceCarrier.{u, v} 2 :=
  strictOriginalFibrantFactorizationData.originalFactorizationFunctor

omit B in
/-- Every arbitrary source I Arrow square keeps original source/Z/target maps together. -/
theorem sourceI_map_fields [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {a b : Arrow SourceCarrier.{u, v}}
  (φ : a ⟶ b) :
    (originalCofibrantFactorizationData.originalFactorizationFunctor.map φ).app 0 = φ.left ∧
    (originalCofibrantFactorizationData.originalFactorizationFunctor.map φ).app 1 =
      originalCofibrantFactorizationData.Z.map φ ∧
      (originalCofibrantFactorizationData.originalFactorizationFunctor.map φ).app 2 = φ.right :=
  originalCofibrantFactorizationData.originalFactorizationFunctor_map_fields φ

omit B in
/-- Every arbitrary source J Arrow square keeps original source/Z/target maps together. -/
theorem sourceJ_map_fields [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {a b : Arrow SourceCarrier.{u, v}}
  (φ : a ⟶ b) :
    (originalFibrantFactorizationData.originalFactorizationFunctor.map φ).app 0 = φ.left ∧
    (originalFibrantFactorizationData.originalFactorizationFunctor.map φ).app 1 =
      originalFibrantFactorizationData.Z.map φ ∧
      (originalFibrantFactorizationData.originalFactorizationFunctor.map φ).app 2 = φ.right :=
  originalFibrantFactorizationData.originalFactorizationFunctor_map_fields φ

omit B in
/-- The original source I full diagram has exactly the original complete caller composite. -/
theorem sourceI_fac [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (a : Arrow SourceCarrier.{u, v}) :
    (originalCofibrantFactorizationData.originalFactorizationFunctor.obj a).hom = a.hom :=
  originalCofibrantFactorizationData.originalFactorizationFunctor_fac a

omit B in
/-- The original source J full diagram has exactly the original complete caller composite. -/
theorem sourceJ_fac [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (a : Arrow SourceCarrier.{u, v}) :
    (originalFibrantFactorizationData.originalFactorizationFunctor.obj a).hom = a.hom :=
  originalFibrantFactorizationData.originalFactorizationFunctor_fac a

/-- The actual strict/source full I diagram comparison uses the supplied original strict counit. -/
def strictIComparisonIso :
    strictI.{u, v} ⋙ EnrichedZeroCompletion.strictRestriction.mapComposableArrows 2 ≅
      EnrichedZeroCompletion.strictRestriction.mapArrow ⋙ sourceI.{u, v} :=
  originalCofibrantFactorizationData.originalWholeFactorizationEquivalenceIso
    (BasedNativePresentation.strictEquivalence (A := PointedCGWH.SymmetricDRight.Index))

/-- The actual strict/source full J diagram comparison uses the supplied original strict counit. -/
def strictJComparisonIso :
    strictJ.{u, v} ⋙ EnrichedZeroCompletion.strictRestriction.mapComposableArrows 2 ≅
      EnrichedZeroCompletion.strictRestriction.mapArrow ⋙ sourceJ.{u, v} :=
  originalFibrantFactorizationData.originalWholeFactorizationEquivalenceIso
    (BasedNativePresentation.strictEquivalence (A := PointedCGWH.SymmetricDRight.Index))

end PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalWholeData
