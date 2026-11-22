/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.SourceProducers.OrdinalModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.NativeOrdinalCompactSources

/-!
# Original native generating endpoints on full coefficient-orbit cell histories

The carrier is the actual native symmetric operator-spectrum category. The
generators are the literal enriched free images of the original freely pointed
realized boundary and horn maps. Compact separable endpoint Hom is transported
through the actual costar/free/evaluation adjunction.

The whole arbitrary product-Sigma coefficient action and repeated finite
pushout product are retained when proving closedness. The same closed class
then controls the full cofibration-orbit cellular closure. Both original
generator endpoints preserve each original closed linear diagram and cocone.

This is the native source argument in Pavlov--Scholbach,
arXiv:1510.04969v3, §7.5, and arXiv:1410.5699v2, Appendix 9.1 and 9.3.
No local presentability, combinatoriality, or pretty smallness of pointed
CGWH is asserted. This file supplies source smallness; acyclic symmetric
h-monoidality of a positive stable model is a separate upstream producer.
-/

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory Limits MorphismProperty MonoidalCategory Opposite
open CategoryTheory.EnrichedFunctorCat
open CategoryTheory.OperadicOrbitCells
open CategoryTheory.OperadicOrbitCells.ProfileGeometry
open CategoryTheory.SmallObject.CellularNormalization
open HomotopicalAlgebra
open PointedCGWH TopologicalSpace
open scoped MonoidalClosed CGWH.modelCategory

namespace HomotopicalAlgebra.OperadicTransfer.SourceProducers.NativeClosedSources

/-- The actual original native symmetric carrier, rather than a Day R-module alias. -/
abbrev Carrier := PointedCGWH.NativeClosedCellHistory.Carrier.{u, v}

attribute [local instance] copowerUnderlyingEnrichedOrdinary
  copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

/-- Every original operator value tests the same native map. -/
abbrev closedInclusions : MorphismProperty Carrier.{u, v} :=
  PointedCGWH.NativeClosedCellHistory.closedInclusions

/-- Each original generator retains its actual operator and CGWH arrow label. -/
abbrev originalGenerators (K : MorphismProperty CGWH.{u, v}) :
    MorphismProperty Carrier.{u, v} :=
  EnrichedProjective.generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
    (K.strictMap (Under.costar CGWH.point))

/-- Literal costar and native free/evaluation Hom preserves the original
closed linear diagram, with no continuity or auxiliary rank restriction. -/
theorem freeCompactSource_preservesClosedLinearColimit
    (a : PointedCGWH.SymmetricOperatorIndex.{u, v}) (A : CGWH.{u, v})
    [CompactSpace A] [SeparableSpace A]
    {T : Type v} [LinearOrder T] [OrderBot T] (D : T ⥤ Carrier.{u, v})
    (hD : ∀ ⦃i j : T⦄ (f : i ⟶ j), closedInclusions (D.map f)) :
    PreservesColimit D (coyoneda.obj (op
      ((EnrichedFunctorCat.Free.functor a).obj ((Under.costar CGWH.point).obj A)))) := by
  let ev := EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) a
  let U := PointedCGWH.pointedToCGWH.{u, v}
  let : IsConnected T := IsFiltered.isConnected T
  let : PreservesColimit D (ev ⋙ U) := inferInstance
  have hF : ∀ ⦃i j : T⦄ (f : i ⟶ j),
      Topology.IsClosedEmbedding (ConcreteCategory.hom ((D ⋙ ev ⋙ U).map f)) := by
    intro i j f
    exact hD f a
  let : PreservesColimit (D ⋙ ev ⋙ U) (coyoneda.obj (op A)) :=
    CGWH.compactSeparable_preservesClosedLinearColimit A (D ⋙ ev ⋙ U) hF
  exact ((Under.costarAdjForget CGWH.point).comp
    (EnrichedFunctorCat.Free.adjunction a)).preservesColimit_leftAdjointSource A D

private def endpointProperty (H : Carrier.{u, v} → Prop) : MorphismProperty Carrier.{u, v} :=
  fun A B _ => H A ∧ H B

/-- Both endpoints are the actual freely pointed realized endpoints,
transported through their original full free Arrow, not just arrow-set size. -/
theorem originalGeneratorEndpoints_preserveClosedLinearColimit
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {T : Type v} [LinearOrder T] [OrderBot T] (D : T ⥤ Carrier.{u, v})
    (hD : ∀ ⦃i j : T⦄ (f : i ⟶ j), closedInclusions (D.map f))
    {X Y : Carrier.{u, v}} (i : X ⟶ Y) (hi : originalGenerators K i) :
    PreservesColimit D (coyoneda.obj (op X)) ∧
      PreservesColimit D (coyoneda.obj (op Y)) := by
  let H : Carrier.{u, v} → Prop := fun X => PreservesColimit D (coyoneda.obj (op X))
  have h : originalGenerators K ≤ endpointProperty H := by
    rw [originalGenerators, EnrichedProjective.generators, adjointFamilyGenerators_eq_iSup_strictMap]
    refine iSup_le fun a => ?_
    rw [strictMap_le_iff_le_inverseImage, strictMap_le_iff_le_inverseImage]
    intro A B g hg
    have hEndpoints := CGWH.realizedGeneratorEndpoints_compactSeparable g (hK _ hg)
    let : CompactSpace A := hEndpoints.1.1
    let : SeparableSpace A := hEndpoints.1.2
    let : CompactSpace B := hEndpoints.2.1
    let : SeparableSpace B := hEndpoints.2.2
    exact ⟨freeCompactSource_preservesClosedLinearColimit a A D hD,
      freeCompactSource_preservesClosedLinearColimit a B D hD⟩
  exact h i hi

/-- Hom from both original generator endpoints preserves every bottomed
well-ordered closed diagram required by the full ordinal A6 producer. -/
theorem originalGeneratorSourceHomClosed
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions) :
    SourceHomPreservation.{_, _, v} (originalGenerators K) closedInclusions where
  domains i := by
    intro T _ _ _ D hD
    exact (originalGeneratorEndpoints_preserveClosedLinearColimit K hK D
      (fun {_ _} f => hD _ _ f) i.1.hom i.2).1
  codomains i := by
    intro T _ _ _ D hD
    exact (originalGeneratorEndpoints_preserveClosedLinearColimit K hK D
      (fun {_ _} f => hD _ _ f) i.1.hom i.2).2

/-- Every leg of the caller's actual closed colimit remains colimiting after
Hom from either of the literal original generating endpoints. -/
def mappedOriginalGeneratorEndpointCocones
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {T : Type v} [LinearOrder T] [OrderBot T] (D : T ⥤ Carrier.{u, v})
    (hD : ∀ ⦃i j : T⦄ (f : i ⟶ j), closedInclusions (D.map f))
    {X Y : Carrier.{u, v}} (i : X ⟶ Y) (hi : originalGenerators K i)
    (c : Cocone D) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (op X)).mapCocone c) ×
      IsColimit ((coyoneda.obj (op Y)).mapCocone c) := by
  letI : PreservesColimit D (coyoneda.obj (op X)) :=
    (originalGeneratorEndpoints_preserveClosedLinearColimit K hK D hD i hi).1
  letI : PreservesColimit D (coyoneda.obj (op Y)) :=
    (originalGeneratorEndpoints_preserveClosedLinearColimit K hK D hD i hi).2
  exact ⟨isColimitOfPreserves _ hc, isColimitOfPreserves _ hc⟩

section NativeCofibrationCells

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] EnrichedProjective.Native.modelCategory

/-- The full product-Sigma coefficient action and expanded repeated PP
are retained when proving closedness of an original positive family. -/
theorem originalOrbitFamilyClosed (s : PositiveOrbitFamily Carrier.{u, v})
    (hs : ∀ r, cofibrations Carrier.{u, v} (s.arrows r).hom) :
    closedInclusions (familyOrbitArrow s).hom := by
  apply PointedCGWH.NativeClosedCellHistory.coefficientOrbitClosed s.coefficient
  exact PointedCGWH.NativeClosedCellHistory.iteratedPushoutProductCofibration
    (multiplicityProfile_inputCount_pos s.colors_pos s.multiplicity s.multiplicity_pos)
    (profileArrowFamily (matrixArrowFamily s.arrows) (multiplicityProfile s.colors_pos s.multiplicity))
    (fun i => hs _)

/-- Every original arbitrary-coefficient finite orbit generator is closed. -/
theorem originalOrbitGeneratorsClosed :
    orbitGenerators (cofibrations Carrier.{u, v}) ≤ closedInclusions :=
  (orbitGenerators_le_iff _ _).2 originalOrbitFamilyClosed

/-- The complete coproduct/pushout/transfinite closure of the original
cofibration orbit arrows stays in the actual evaluated closed class. -/
theorem originalCofibrationCellsClosed :
    OperadicAcyclicCells.cofibrationCells.{v, v} Carrier.{u, v} ≤ closedInclusions := by
  let : closedInclusions.{u, v}.IsStableUnderTransfiniteComposition.{v} :=
    PointedCGWH.NativeClosedCellHistory.closedInclusions_isStableUnderTransfiniteComposition
  have hCop : (orbitGenerators (cofibrations Carrier.{u, v})).coproducts.{v} ≤ closedInclusions :=
    (coproducts_le_iff (P := orbitGenerators (cofibrations Carrier.{u, v}))).2 originalOrbitGeneratorsClosed
  have hPush : (orbitGenerators (cofibrations Carrier.{u, v})).coproducts.{v}.pushouts ≤ closedInclusions :=
    (pushouts_le_iff (P := (orbitGenerators (cofibrations Carrier.{u, v})).coproducts.{v})).2 hCop
  have hTrans : closedInclusions.{u, v}.transfiniteCompositions.{v} ≤ closedInclusions.{u, v} :=
    transfiniteCompositions_le.{v} closedInclusions.{u, v}
  exact (transfiniteCompositions_monotone hPush).trans hTrans

/-- Both original generating endpoints preserve the same full actual
cofibration-cell diagrams required by operadic ordinal acyclic closure. -/
theorem originalGeneratorSourceHomCells
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions) :
    SourceHomPreservation.{_, _, v} (originalGenerators K)
      (OperadicAcyclicCells.cofibrationCells.{v, v} Carrier.{u, v}) where
  domains i := by
    intro T _ _ _ D hD
    exact (originalGeneratorSourceHomClosed K hK).domains i T D
      (fun a b f => originalCofibrationCellsClosed _ (hD a b f))
  codomains i := by
    intro T _ _ _ D hD
    exact (originalGeneratorSourceHomClosed K hK).codomains i T D
      (fun a b f => originalCofibrationCellsClosed _ (hD a b f))

/-- The canonical original native I family has both endpoint source
comparisons on the genuine arbitrary-coefficient cell class. -/
theorem originalISourceHomCells :
    SourceHomPreservation.{_, _, v}
      (EnrichedProjective.generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        PointedCGWH.realizedBoundaryInclusions.{u, v})
      (OperadicAcyclicCells.cofibrationCells.{v, v} Carrier.{u, v}) :=
  originalGeneratorSourceHomCells CGWH.realizedBoundaryInclusions le_sup_left

/-- The original native free-horn family retains the same endpoint Hom
comparisons. This is the level J family, not a substituted stable J bank. -/
theorem originalLevelJSourceHomCells :
    SourceHomPreservation.{_, _, v}
      (EnrichedProjective.generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        PointedCGWH.realizedHornInclusions.{u, v})
      (OperadicAcyclicCells.cofibrationCells.{v, v} Carrier.{u, v}) :=
  originalGeneratorSourceHomCells CGWH.realizedHornInclusions le_sup_right

end NativeCofibrationCells


end HomotopicalAlgebra.OperadicTransfer.SourceProducers.NativeClosedSources
