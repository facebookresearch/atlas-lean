/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.OriginalIntegerCriterion
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionIntegerPiDetection
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOrthogonalRawPiHEPPushoutGluing

/-!
# Original orthogonal Omega tests of genuine HEP caller pushouts

The source span is the actual same-I approximation of the complete caller
span. Its original three counits and both caller pushout legs are retained.
The comparison is first proved an integer equivalence by the original HEP
gluing theorem, then tested by the actual function-spectrum telescope and
its original level-homotopy Hom retract.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The original integer comparison of a genuine HEP span has every original
Omega-target level-homotopy test, with both complete caller pushouts fixed. -/
theorem originalSpanCallerComparison_omegaTests
    (D : WalkingSpan ⥤ Actual.OrthogonalCarrier.{u, v})
    {Q P : Actual.OrthogonalCarrier.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property
      (D.map WalkingSpan.Hom.fst)) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v}
      (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) :=
  MMSSStabilization.OriginalFunctionRawIteration.integerPiStar_implies_omegaTests
    (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP)
    (originalOrthogonalSpanCallerComparison_integerPi D lQ rQ sqQ lP rP sqP hi)

/-- Every original Omega target tests the same complete comparison map by
precomposition in the original level homotopy category. -/
theorem originalSpanCallerComparison_precomp_bijective
    (D : WalkingSpan ⥤ Actual.OrthogonalCarrier.{u, v})
    {Q P : Actual.OrthogonalCarrier.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property
      (D.map WalkingSpan.Hom.fst))
    (E : Actual.OrthogonalCarrier.{u, v}) (hE : Actual.OrthogonalIsOmega E) :
    Function.Bijective
      (fun g : (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).obj P ⟶
        (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).obj E =>
          (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
            (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) ≫ g) :=
  originalSpanCallerComparison_omegaTests D lQ rQ sqQ lP rP sqP hi E hE

/-- The source comparison transfers the resolved pushout theorem to the
original HEP caller span, without any cofibrancy assumption on its endpoints. -/
theorem originalHEPSpanPushout_omegaTests
    (D : WalkingSpan ⥤ Actual.OrthogonalCarrier.{u, v})
    {Q P : Actual.OrthogonalCarrier.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property
      (D.map WalkingSpan.Hom.fst))
    (hD : NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v}
      (D.map WalkingSpan.Hom.fst)) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v} rP := by
  let W := NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v}
  let comparison := originalSpanCallerComparison D lQ rQ sqQ lP rP sqP
  have hComparison : W comparison :=
    originalSpanCallerComparison_omegaTests D lQ rQ sqQ lP rP sqP hi
  have hResolved : W rQ :=
    originalResolvedSpanPushout_omegaTests Actual.orthogonalFamily D lQ rQ sqQ hD
  have hRightCounit : W ((originalSpanCounit (B := B) D).app WalkingSpan.right) :=
    NativeK.levelWeak_le_omegaTests Actual.orthogonalFamily _
      (originalSpanCounit_levelWeak D WalkingSpan.right)
  have hComposite : W (rQ ≫ comparison) := W.comp_mem _ _ hResolved hComparison
  have hLeg : rQ ≫ comparison =
      (originalSpanCounit (B := B) D).app WalkingSpan.right ≫ rP :=
    originalSpanCallerComparison_right D lQ rQ sqQ lP rP sqP
  exact W.of_precomp _ _ hRightCounit (hLeg ▸ hComposite)

/-- Cobase change of an actual original HEP Omega equivalence is an original
Omega equivalence for every caller pushout and arbitrary endpoints. -/
theorem originalHEPPushout_omegaTests
    {A X Z P : Actual.OrthogonalCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout i z kX kZ)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hW : NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v} i) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v} kZ := by
  let D := span i z
  let DQ := originalSpanDiagram (B := B) D
  let lQ : DQ.obj WalkingSpan.left ⟶
      pushout (DQ.map WalkingSpan.Hom.fst) (DQ.map WalkingSpan.Hom.snd) :=
    pushout.inl _ _
  let rQ : DQ.obj WalkingSpan.right ⟶
      pushout (DQ.map WalkingSpan.Hom.fst) (DQ.map WalkingSpan.Hom.snd) :=
    pushout.inr _ _
  exact originalHEPSpanPushout_omegaTests D lQ rQ
    (IsPushout.of_hasPushout _ _) kX kZ sq hi hW

/-- Genuine HEP pushout comparison for the same two caller squares, all eight
arbitrary endpoints, and all four original vertical maps. -/
theorem originalHEPPushoutComparison_omegaTests
    {A X Z P A' X' Z' P' : Actual.OrthogonalCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hi' : PointedCGWH.EnrichedBasedHomotopyExtension.property i')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (d : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ d) (hP : c ≫ kZ' = kZ ≫ d)
    (ha : NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v} a)
    (hb : NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v} b)
    (hc : NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v} c) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v} d :=
  MMSSStabilization.OriginalFunctionRawIteration.integerPiStar_implies_omegaTests d
    (originalOrthogonalRawPiHEPpushoutGluing
      i z kX kZ i' z' kX' kZ' sq sq' hi hi' a b c d hI hZ hX hP
      ((OriginalIntegerCriterionComplete.originalOmegaTests_iff_integerPiStar (B := B) a).mp ha)
      ((OriginalIntegerCriterionComplete.originalOmegaTests_iff_integerPiStar (B := B) b).mp hb)
      ((OriginalIntegerCriterionComplete.originalOmegaTests_iff_integerPiStar (B := B) c).mp hc))

/-- The original conjunction of genuine HEP and all Omega tests. -/
def originalHEPOmega : MorphismProperty Actual.OrthogonalCarrier.{u, v} :=
  PointedCGWH.EnrichedBasedHomotopyExtension.property ⊓
    NativeK.omegaTests (B := B) Actual.orthogonalFamily

/-- The actual HEP and Omega class is closed under every full caller cobase
square with arbitrary endpoints. -/
instance originalHEPOmega_cobase : (originalHEPOmega (B := B)).IsStableUnderCobaseChange where
  of_isPushout sq hi :=
    ⟨MorphismProperty.of_isPushout sq hi.1,
      originalHEPPushout_omegaTests _ _ _ _ sq.flip hi.1 hi.2⟩

end PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure
