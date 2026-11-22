/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderBasedHEP
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderCoproduct
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableCoproductClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeHEPOmegaPushoutComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOmegaMappingOrdinalClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOrthogonalRawPiHEPPushoutGluing
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalSymmetricPiStarOmegaDetectionClosed
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialStableModelProperties
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOrthogonalOmegaCoproductClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableHEPOrdinalWeakComparison
import MathlibExt.CategoryTheory.MorphismProperty.CoproductClosure

/-!
# Original stable StableCellularClosure

The complete original sequential, symmetric and orthogonal carriers, maps,
caller cardinal/bottom and all permitted universes are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits

private theorem stableNativeHasCoproduct {I : Type} [CategoryTheory.EnrichedCategory
  PointedCGWH.{u, v} I]
    {J : Type v} (X : J → CategoryTheory.EnrichedFunctorCat PointedCGWH.{u, v} I) : HasCoproduct
      X := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.nativeColimits
  let h : HasColimitsOfSize.{v, v} (CategoryTheory.EnrichedFunctorCat PointedCGWH.{u, v} I) := by
    infer_instance
  let _ : HasColimitsOfShape (Discrete J) (CategoryTheory.EnrichedFunctorCat PointedCGWH.{u, v}
    I) :=
    @HasColimitsOfSize.has_colimits_of_shape (CategoryTheory.EnrichedFunctorCat PointedCGWH.{u,
      v} I) _ h (Discrete J) _
  exact HasColimitsOfShape.has_colimit (Discrete.functor X)

private theorem stableNativeHasProducts (J : Type v) : HasProductsOfShape J PointedCGWH.{u, v} := by
  let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} := CGWH.limits.instHasLimitsOfSize
  let h : HasLimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasLimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  exact @HasLimitsOfSize.has_limits_of_shape PointedCGWH.{u, v} _ h (Discrete J) _

attribute [local instance] stableNativeHasCoproduct stableNativeHasProducts

section SymmetricHEPSpan01

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.SymmetricIntegerHomotopy
open PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit B in
/-- The literal original symmetric restriction preserves the caller's full
pushout square and both original legs. -/
private theorem originalRestriction_pushout
    {A X Z P : Actual.SymmetricCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout i z kX kZ) :
    IsPushout (underlyingSequential.map i) (underlyingSequential.map z)
      (underlyingSequential.map kX) (underlyingSequential.map kZ) :=
  originalRestriction_isPushout
    CategoryTheory.Spectra.SpectrumIndexMaps.sequentialSymmetricOperatorIndexFunctor
    i z kX kZ sq

omit B in
/-- Every original HEP map keeps its actual free-time extension under the
unchanged sequential restriction. -/
private theorem originalRestriction_HEP
    {A X : Actual.SymmetricCarrier.{u, v}} (i : A ⟶ X)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property (underlyingSequential.map i) :=
  PointedCGWH.EnrichedBasedHomotopyExtension.originalRestriction_mem
    CategoryTheory.Spectra.SpectrumIndexMaps.sequentialSymmetricOperatorIndexFunctor i hi

/-- The actual integer maps of both caller HEP pushouts are compared on the
original symmetric restriction, retaining all eight endpoints and four squares. -/
private theorem originalRawPiHEPPushoutComparison
    {A X Z P A' X' Z' P' : Actual.SymmetricCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hi' : PointedCGWH.EnrichedBasedHomotopyExtension.property i')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (p : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ p) (hP : c ≫ kZ' = kZ ≫ p)
    (ha : integerPiStarEquivalences a) (hb : integerPiStarEquivalences b)
    (hc : integerPiStarEquivalences c) : integerPiStarEquivalences p := by
  let R := underlyingSequential.{u, v}
  have hRI : R.map a ≫ R.map i' = R.map i ≫ R.map b :=
    (R.map_comp _ _).symm.trans ((R.congr_map hI).trans (R.map_comp _ _))
  have hRZ : R.map a ≫ R.map z' = R.map z ≫ R.map c :=
    (R.map_comp _ _).symm.trans ((R.congr_map hZ).trans (R.map_comp _ _))
  have hRX : R.map b ≫ R.map kX' = R.map kX ≫ R.map p :=
    (R.map_comp _ _).symm.trans ((R.congr_map hX).trans (R.map_comp _ _))
  have hRP : R.map c ≫ R.map kZ' = R.map kZ ≫ R.map p :=
    (R.map_comp _ _).symm.trans ((R.congr_map hP).trans (R.map_comp _ _))
  apply (integerPiStarEquivalences_iff_underlying p).mpr
  exact PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing.originalRawPiHEPpushoutGluing
    (R.map i) (R.map z) (R.map kX) (R.map kZ)
    (R.map i') (R.map z') (R.map kX') (R.map kZ')
    (originalRestriction_pushout i z kX kZ sq)
    (originalRestriction_pushout i' z' kX' kZ' sq')
    (originalRestriction_HEP i hi) (originalRestriction_HEP i' hi')
    (R.map a) (R.map b) (R.map c) (R.map p) hRI hRZ hRX hRP
    ((integerPiStarEquivalences_iff_underlying a).mp ha)
    ((integerPiStarEquivalences_iff_underlying b).mp hb)
    ((integerPiStarEquivalences_iff_underlying c).mp hc)

/-- The three original level-weak source counits prove integer weakness of
the same caller comparison of the actual complete HEP span. -/
private theorem originalSpanCallerComparison_integerPi
    (D : WalkingSpan ⥤ Actual.SymmetricCarrier.{u, v})
    {Q P : Actual.SymmetricCarrier.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property
      (D.map WalkingSpan.Hom.fst)) :
    integerPiStarEquivalences (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) := by
  let e := originalSpanCounit (B := B) D
  exact originalRawPiHEPPushoutComparison
    ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
    ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ
    (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP sqQ sqP
    (originalSpanDiagram_HEP D).1 hi
    (e.app WalkingSpan.zero) (e.app WalkingSpan.left) (e.app WalkingSpan.right)
    (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP)
    (e.naturality WalkingSpan.Hom.fst).symm
    (e.naturality WalkingSpan.Hom.snd).symm
    (originalSpanCallerComparison_left D lQ rQ sqQ lP rP sqP).symm
    (originalSpanCallerComparison_right D lQ rQ sqQ lP rP sqP).symm
    (levelWeak_le_integerPiStarEquivalences _ (originalSpanCounit_levelWeak D WalkingSpan.zero))
    (levelWeak_le_integerPiStarEquivalences _ (originalSpanCounit_levelWeak D WalkingSpan.left))
    (levelWeak_le_integerPiStarEquivalences _ (originalSpanCounit_levelWeak D WalkingSpan.right))

/-- The closed original forward detector gives all Omega tests of the same
comparison, with no Omega or cofibrancy condition on any caller endpoint. -/
private theorem originalSpanCallerComparison_omegaTests
    (D : WalkingSpan ⥤ Actual.SymmetricCarrier.{u, v})
    {Q P : Actual.SymmetricCarrier.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property
      (D.map WalkingSpan.Hom.fst)) :
    NativeK.omegaTests Actual.symmetricFamily
      (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) :=
  PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests.integerIsos_imply_omegaTests _
    ((integerPiStarEquivalences_iff _).mp
      (originalSpanCallerComparison_integerPi D lQ rQ sqQ lP rP sqP hi))

/-- The genuine source comparison transfers the resolved Omega pushout
private theorem to every original HEP caller span and its actual two pushout legs. -/
private theorem originalHEPSpanPushout_omegaTests
    (D : WalkingSpan ⥤ Actual.SymmetricCarrier.{u, v})
    {Q P : Actual.SymmetricCarrier.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property
      (D.map WalkingSpan.Hom.fst))
    (hD : NativeK.omegaTests Actual.symmetricFamily (D.map WalkingSpan.Hom.fst)) :
    NativeK.omegaTests Actual.symmetricFamily rP := by
  let W := NativeK.omegaTests (B := B) Actual.symmetricFamily.{u, v}
  let p := originalSpanCallerComparison D lQ rQ sqQ lP rP sqP
  have hComparison : W p := originalSpanCallerComparison_omegaTests D lQ rQ sqQ lP rP sqP hi
  have hResolved : W rQ := originalResolvedSpanPushout_omegaTests
    Actual.symmetricFamily D lQ rQ sqQ hD
  have hCounit : W ((originalSpanCounit (B := B) D).app WalkingSpan.right) :=
    NativeK.levelWeak_le_omegaTests Actual.symmetricFamily _
      (originalSpanCounit_levelWeak D WalkingSpan.right)
  have hComposite : W (rQ ≫ p) := W.comp_mem _ _ hResolved hComparison
  have hLeg : rQ ≫ p = (originalSpanCounit (B := B) D).app WalkingSpan.right ≫ rP :=
    originalSpanCallerComparison_right D lQ rQ sqQ lP rP sqP
  exact W.of_precomp _ _ hCounit (hLeg ▸ hComposite)

/-- Every actual symmetric HEP stable equivalence retains stable weakness
after every caller cobase change, with arbitrary original endpoints. -/
private theorem originalHEPPushout_omegaTests
    {A X Z P : Actual.SymmetricCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout i z kX kZ)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hW : NativeK.omegaTests Actual.symmetricFamily i) :
    NativeK.omegaTests Actual.symmetricFamily kZ := by
  let D := span i z
  let DQ := originalSpanDiagram (B := B) D
  exact originalHEPSpanPushout_omegaTests D (pushout.inl _ _) (pushout.inr _ _)
    (IsPushout.of_hasPushout (DQ.map WalkingSpan.Hom.fst) (DQ.map WalkingSpan.Hom.snd))
    kX kZ sq hi hW

/-- The literal conjunction of original based HEP and all original Omega tests. -/
private def originalHEPOmega : MorphismProperty Actual.SymmetricCarrier.{u, v} :=
  PointedCGWH.EnrichedBasedHomotopyExtension.property ⊓ NativeK.omegaTests Actual.symmetricFamily

/-- The original HEP/Omega class is closed under every actual caller pushout. -/
private instance originalHEPOmega_cobase : (originalHEPOmega (B := B)).IsStableUnderCobaseChange
  where
  of_isPushout sq hi :=
    ⟨MorphismProperty.of_isPushout sq hi.1,
      originalHEPPushout_omegaTests _ _ _ _ sq.flip hi.1 hi.2⟩


end PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure

end SymmetricHEPSpan01

section SymmetricHEPComparison02

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Every actual component of the same-I span approximation preserves the
original Omega condition through its two genuine level-weak counit maps. -/
private theorem originalSpanMap_stage_omegaTests
    {D E : WalkingSpan ⥤ Actual.SymmetricCarrier.{u, v}} (α : D ⟶ E)
    (hα : ∀ j : WalkingSpan, NativeK.omegaTests Actual.symmetricFamily (α.app j))
    (j : WalkingSpan) :
    NativeK.omegaTests Actual.symmetricFamily ((originalSpanMap (B := B) α).app j) := by
  let W := NativeK.omegaTests (B := B) Actual.symmetricFamily.{u, v}
  have hD : W ((originalSpanCounit (B := B) D).app j) :=
    NativeK.levelWeak_le_omegaTests Actual.symmetricFamily _ (originalSpanCounit_levelWeak D j)
  have hE : W ((originalSpanCounit (B := B) E).app j) :=
    NativeK.levelWeak_le_omegaTests Actual.symmetricFamily _ (originalSpanCounit_levelWeak E j)
  have h := W.comp_mem _ _ hD (hα j)
  have hn := congrArg (fun p => p.app j)
    ((originalSpanCounitNatTrans (B := B)).naturality α)
  change (originalSpanMap (B := B) α).app j ≫ (originalSpanCounit (B := B) E).app j =
    (originalSpanCounit (B := B) D).app j ≫ α.app j at hn
  rw [← hn] at h
  exact W.of_postcomp _ _ hE h

/-- The original three-map Omega comparison passes through the two genuine
resolved spans and back to the same two caller HEP pushouts. -/
theorem originalHEPPushoutComparison_omegaTests
    {A X Z P A' X' Z' P' : Actual.SymmetricCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hi' : PointedCGWH.EnrichedBasedHomotopyExtension.property i')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (p : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ p) (hP : c ≫ kZ' = kZ ≫ p)
    (ha : NativeK.omegaTests Actual.symmetricFamily a)
    (hb : NativeK.omegaTests Actual.symmetricFamily b)
    (hc : NativeK.omegaTests Actual.symmetricFamily c) :
    NativeK.omegaTests Actual.symmetricFamily p := by
  let W := NativeK.omegaTests (B := B) Actual.symmetricFamily.{u, v}
  let D := span i z
  let E := span i' z'
  let α : D ⟶ E := spanHomMk a b c hI.symm hZ.symm
  let DQ := originalSpanDiagram (B := B) D
  let EQ := originalSpanDiagram (B := B) E
  let β : DQ ⟶ EQ := originalSpanMap (B := B) α
  let QD := pushout (DQ.map WalkingSpan.Hom.fst) (DQ.map WalkingSpan.Hom.snd)
  let QE := pushout (EQ.map WalkingSpan.Hom.fst) (EQ.map WalkingSpan.Hom.snd)
  let lQD : DQ.obj WalkingSpan.left ⟶ QD := pushout.inl _ _
  let rQD : DQ.obj WalkingSpan.right ⟶ QD := pushout.inr _ _
  let lQE : EQ.obj WalkingSpan.left ⟶ QE := pushout.inl _ _
  let rQE : EQ.obj WalkingSpan.right ⟶ QE := pushout.inr _ _
  have sQD : IsPushout (DQ.map WalkingSpan.Hom.fst) (DQ.map WalkingSpan.Hom.snd) lQD rQD :=
    IsPushout.of_hasPushout _ _
  have sQE : IsPushout (EQ.map WalkingSpan.Hom.fst) (EQ.map WalkingSpan.Hom.snd) lQE rQE :=
    IsPushout.of_hasPushout _ _
  have hComm : DQ.map WalkingSpan.Hom.fst ≫ (β.app WalkingSpan.left ≫ lQE) =
      DQ.map WalkingSpan.Hom.snd ≫ (β.app WalkingSpan.right ≫ rQE) := by
    rw [← Category.assoc, β.naturality WalkingSpan.Hom.fst, Category.assoc, sQE.w,
      ← Category.assoc, ← β.naturality WalkingSpan.Hom.snd, Category.assoc]
  let q : QD ⟶ QE := sQD.desc (β.app WalkingSpan.left ≫ lQE)
    (β.app WalkingSpan.right ≫ rQE) hComm
  have hQL : lQD ≫ q = β.app WalkingSpan.left ≫ lQE := sQD.inl_desc _ _ _
  have hQR : rQD ≫ q = β.app WalkingSpan.right ≫ rQE := sQD.inr_desc _ _ _
  have hα (j : WalkingSpan) : W (α.app j) := by
    rcases j with (_ | (_ | _))
    · exact ha
    · exact hb
    · exact hc
  have hβ (j : WalkingSpan) : W (β.app j) := originalSpanMap_stage_omegaTests α hα j
  have hiQD : ∀ j : PointedCGWH.SymmetricOperatorIndex.{u, v},
      Cofibration ((evaluation j).map (DQ.map WalkingSpan.Hom.fst)) :=
    PointedCGWH.Spectra.NativeHEPOmegaPushoutComparison.symmetric_nativeCofibration_component _
      (originalSpanLeg_cofibration WalkingSpan.left WalkingSpan.Hom.fst D)
  have hiQE : ∀ j : PointedCGWH.SymmetricOperatorIndex.{u, v},
      Cofibration ((evaluation j).map (EQ.map WalkingSpan.Hom.fst)) :=
    PointedCGWH.Spectra.NativeHEPOmegaPushoutComparison.symmetric_nativeCofibration_component _
      (originalSpanLeg_cofibration WalkingSpan.left WalkingSpan.Hom.fst E)
  have hq : W q :=
    NativeHEPOmegaPushoutComparison.symmetric_componentCofibrantPushout_comparison_omegaTests
      (DQ.map WalkingSpan.Hom.fst) (DQ.map WalkingSpan.Hom.snd) lQD rQD
      (EQ.map WalkingSpan.Hom.fst) (EQ.map WalkingSpan.Hom.snd) lQE rQE sQD sQE hiQD hiQE
      (β.app WalkingSpan.zero) (β.app WalkingSpan.left) (β.app WalkingSpan.right) q
      (β.naturality WalkingSpan.Hom.fst).symm (β.naturality WalkingSpan.Hom.snd).symm
      hQL.symm hQR.symm (hβ WalkingSpan.zero) (hβ WalkingSpan.left) (hβ WalkingSpan.right)
  let cmpD := originalSpanCallerComparison D lQD rQD sQD kX kZ sq
  let cmpE := originalSpanCallerComparison E lQE rQE sQE kX' kZ' sq'
  have hcmpD : W cmpD := originalSpanCallerComparison_omegaTests D lQD rQD sQD kX kZ sq hi
  have hcmpE : W cmpE := originalSpanCallerComparison_omegaTests E lQE rQE sQE kX' kZ' sq' hi'
  have hn : q ≫ cmpE = cmpD ≫ p :=
    originalSpanCallerComparison_naturality α
      lQD rQD sQD kX kZ sq lQE rQE sQE kX' kZ' sq' q p hQL hQR hX.symm hP.symm
  have hComposite : W (q ≫ cmpE) := W.comp_mem _ _ hq hcmpE
  exact W.of_precomp _ _ hcmpD (hn ▸ hComposite)


end PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure

end SymmetricHEPComparison02

section SymmetricHEPCoproduct03

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.EnrichedIntervalMappingCylinder
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf PointedCGWH.EnrichedMapping.hasSmallLimits

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev C2 := Actual.SymmetricCarrier.{u, v}
private abbrev Q2 := Replacement.cofibrantReplacement (B := B)
  (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev ε2 := Replacement.cofibrantReplacementCounit (B := B)
  (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev W2 := NativeK.omegaTests (B := B) Actual.symmetricFamily.{u, v}

/-- Every actual continuous ordinal retains the original HEP/Omega class
through its same source diagram, bottom map and colimit cocone. -/
private instance originalHEPOmega_transfinite :
    (originalHEPOmega (B := B)).IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    unfold originalHEPOmega
    infer_instance

/-- Every actual coproduct coordinate pushout chain retains original HEP
and every Omega test, including the original empty and dummy coordinates. -/
private instance originalHEPOmega_coproducts :
    (originalHEPOmega (B := B)).IsStableUnderCoproducts.{v} :=
  MorphismProperty.isStableUnderCoproducts_of_cobase_transfinite (originalHEPOmega (B := B))

/-- The complete original coproduct of HEP/Omega maps belongs to the same
private class through its actual continuous coordinate-chain endpoint. -/
private theorem originalHEPOmega_coproductMap {J : Type v}
    {X Y : J → C2.{u, v}} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, originalHEPOmega (B := B) (f j)) :
    originalHEPOmega (B := B) (Limits.Sigma.map f) :=
  MorphismProperty.coproductMap_mem_of_cobase_transfinite (originalHEPOmega (B := B)) f hf

/-- The exact original Q2 counit square preserves every Omega-test map on
its two original I-approximations. -/
private theorem originalQMap_omegaTests {X Y : C2.{u, v}} (f : X ⟶ Y) (hf : W2 (f)) : W2 (Q2.map
  f) := by
  have hX : W2 (ε2.app X) := NativeK.levelWeak_le_omegaTests Actual.symmetricFamily _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X)
  have hY : W2 (ε2.app Y) := NativeK.levelWeak_le_omegaTests Actual.symmetricFamily _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences Y)
  have h := W2.comp_mem _ _ hX hf
  have hn : Q2.map f ≫ ε2.app Y = ε2.app X ≫ f := ε2.naturality f
  rw [← hn] at h
  exact W2.of_postcomp _ _ hY h

/-- The original coproduct of all I-counits is Omega weak by its actual
mapping cylinders, full source-map coordinate chain and genuine SDR. -/
private theorem originalCoproductCounit_omegaTests {J : Type v} (X : J → C2.{u, v}) :
    W2 (Limits.Sigma.map (fun j => ε2.app (X j))) := by
  let f := fun j => Arrow.mk (ε2.app (X j))
  let i := fun j => source (f j)
  let r := fun j => retraction (f j)
  have hr (j : J) : W2 (r j) :=
    NativeK.levelWeak_le_omegaTests Actual.symmetricFamily _
      ((HomotopicalAlgebra.weakEquivalence_iff _).mp
        (PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.retraction_weakEquivalence (f j)))
  have hi (j : J) : originalHEPOmega (B := B) (i j) := by
    refine ⟨PointedCGWH.EnrichedBasedHomotopyExtension.source_mem (f j), ?_⟩
    have hCounit : W2 (ε2.app (X j)) := NativeK.levelWeak_le_omegaTests Actual.symmetricFamily _
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (X j))
    have hFac : i j ≫ r j = ε2.app (X j) := fac (f j)
    exact W2.of_postcomp _ _ (hr j) (hFac.symm ▸ hCounit)
  have hSource : originalHEPOmega (B := B) (Limits.Sigma.map i) :=
    MorphismProperty.coproductMap_mem_of_cobase_transfinite (originalHEPOmega (B := B)) i hi
  have hRetraction : W2 (Limits.Sigma.map r) :=
    NativeK.levelWeak_le_omegaTests Actual.symmetricFamily _
      (PointedCGWH.EnrichedIntervalMappingCylinder.Coproducts.sigmaRetraction_levelWeak
        (fun j => ε2.app (X j)))
  have hFac : Limits.Sigma.map i ≫ Limits.Sigma.map r =
      Limits.Sigma.map (fun j => ε2.app (X j)) := by
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_map,
      ← Category.assoc, fac, Sigma.ι_map]
    rfl
  exact hFac ▸ W2.comp_mem _ _ hSource.2 hRetraction

/-- Original Q2 coproduct mapping and the two complete counit families
prove every arbitrary-endpoint symmetric coproduct map Omega weak. -/
theorem originalCoproductMap_omegaTests {J : Type v}
    {X Y : J → C2.{u, v}} (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, W2 (f j)) :
    W2 (Limits.Sigma.map f) := by
  let fq := fun j => Q2.map (f j)
  let _ : ∀ j, IsCofibrant (Q2.obj (X j)) :=
    fun j => Replacement.isCofibrant_cofibrantReplacement (X j)
  let _ : ∀ j, IsCofibrant (Q2.obj (Y j)) :=
    fun j => Replacement.isCofibrant_cofibrantReplacement (Y j)
  have hfq : ∀ j, W2 (fq j) := fun j => originalQMap_omegaTests (f j) (hf j)
  have hQ : W2 (Limits.Sigma.map fq) := StableCoproductClosure.omegaTests_sigmaMap
    Actual.symmetricFamily fq hfq
  have hX : W2 (Limits.Sigma.map (fun j => ε2.app (X j))) := originalCoproductCounit_omegaTests X
  have hY : W2 (Limits.Sigma.map (fun j => ε2.app (Y j))) := originalCoproductCounit_omegaTests Y
  have hNat : Limits.Sigma.map fq ≫ Limits.Sigma.map (fun j => ε2.app (Y j)) =
      Limits.Sigma.map (fun j => ε2.app (X j)) ≫ Limits.Sigma.map f := by
    rw [Sigma.map_comp_map, Sigma.map_comp_map]
    apply congrArg (fun g : ∀ j, Q2.obj (X j) ⟶ Y j => Limits.Sigma.map g)
    funext j
    exact ε2.naturality (f j)
  exact W2.of_precomp _ _ hX (hNat ▸ W2.comp_mem _ _ hQ hY)

/-- Both complete original cofan comparisons retain every actual caller
injection and the original caller map, as one whole Arrow isomorphism. -/
private def originalCoproductCallerArrowIso {J : Type v} {X Y : J → C2.{u, v}}
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j) :
    Arrow.mk (Limits.Sigma.map f) ≅ Arrow.mk p := by
  let eX := (coproductIsCoproduct X).coconePointUniqueUpToIso hc
  let eY := (coproductIsCoproduct Y).coconePointUniqueUpToIso hd
  refine Arrow.isoMk eX eY ?_
  change eX.hom ≫ p = Limits.Sigma.map f ≫ eY.hom
  apply Sigma.hom_ext
  intro j
  have hX : Sigma.ι X j ≫ eX.hom = c.inj j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct X) hc ⟨j⟩
  have hY : Sigma.ι Y j ≫ eY.hom = d.inj j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct Y) hd ⟨j⟩
  rw [← Category.assoc, hX, hp, ← Category.assoc, Sigma.ι_map, Category.assoc, hY]

/-- Every actual arbitrary-endpoint map between original colimiting cofans
has all Omega tests, with every original injection and caller square fixed. -/
private theorem originalCofansMap_omegaTests {J : Type v} {X Y : J → C2.{u, v}}
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j) (hf : ∀ j, W2 (f j)) : W2 p :=
  (W2.arrow_mk_iso_iff (originalCoproductCallerArrowIso c hc d hd f p hp)).mp
    (originalCoproductMap_omegaTests f hf)


end PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure

end SymmetricHEPCoproduct03

section SequentialHEPClosure07

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells.Sequential

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev C := PointedCGWH.SequentialSpectrum.{u, v}
/-- The actual sequential stabilization family retains every original generating test. -/
abbrev originalFamily := PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}
private abbrev W := NativeK.omegaTests (B := B) originalFamily.{u, v}

/-- The same actual sequential model and all original integer degrees have the same weak class. -/
theorem omegaTests_eq_integerPiStar : W.{u, v} = integerPiStarEquivalences.{u, v} :=
  NativeStableModels.SequentialStableModelProperties.weakEquivalences_eq_integerPiStar

/-- The original same-source I-span comparison retains every caller pushout leg. -/
private theorem spanCallerComparison_omegaTests
    (D : WalkingSpan ⥤ C.{u, v}) {Q P : C.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property
      (D.map WalkingSpan.Hom.fst)) :
    W (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) := by
  rw [omegaTests_eq_integerPiStar]
  let e := originalSpanCounit (B := B) D
  have hE (j : WalkingSpan) : integerPiStarEquivalences (e.app j) := by
    rw [← omegaTests_eq_integerPiStar]
    exact NativeK.levelWeak_le_omegaTests originalFamily _ (originalSpanCounit_levelWeak D j)
  exact OriginalRawPiHomotopyPushoutGluing.originalRawPiHEPpushoutGluing
    ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
    ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ
    (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP sqQ sqP
    (originalSpanDiagram_HEP D).1 hi
    (e.app WalkingSpan.zero) (e.app WalkingSpan.left) (e.app WalkingSpan.right)
    (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP)
    (e.naturality WalkingSpan.Hom.fst).symm
    (e.naturality WalkingSpan.Hom.snd).symm
    (originalSpanCallerComparison_left D lQ rQ sqQ lP rP sqP).symm
    (originalSpanCallerComparison_right D lQ rQ sqQ lP rP sqP).symm
    (hE WalkingSpan.zero) (hE WalkingSpan.left) (hE WalkingSpan.right)

/-- Cobase change of each original sequential HEP stable arrow is weak on the
caller pushout, retaining the source replacement and both original comparison legs. -/
private theorem originalHEPPushout_omegaTests
    {A X Z P : C.{u, v}} (i : A ⟶ X) (a : A ⟶ Z)
    (x : X ⟶ P) (z : Z ⟶ P) (sq : IsPushout i a x z)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) (hf : W i) : W z := by
  let D := span i a
  let DQ := originalSpanDiagram (B := B) D
  let Q := pushout (DQ.map WalkingSpan.Hom.fst) (DQ.map WalkingSpan.Hom.snd)
  let lQ : DQ.obj WalkingSpan.left ⟶ Q := pushout.inl _ _
  let rQ : DQ.obj WalkingSpan.right ⟶ Q := pushout.inr _ _
  let sQ : IsPushout (DQ.map WalkingSpan.Hom.fst) (DQ.map WalkingSpan.Hom.snd) lQ rQ :=
    IsPushout.of_hasPushout _ _
  let p := originalSpanCallerComparison D lQ rQ sQ x z sq
  have hp : W p := spanCallerComparison_omegaTests D lQ rQ sQ x z sq hi
  have hr : W rQ := originalResolvedSpanPushout_omegaTests originalFamily D lQ rQ sQ hf
  have he : W ((originalSpanCounit (B := B) D).app WalkingSpan.right) :=
    NativeK.levelWeak_le_omegaTests originalFamily _ (originalSpanCounit_levelWeak D _)
  have h := W.comp_mem rQ p hr hp
  rw [originalSpanCallerComparison_right D lQ rQ sQ x z sq] at h
  exact W.of_precomp _ _ he h

/-- The exact three-vertical-leg comparison holds on the two original sequential pushouts. -/
theorem originalHEPPushoutComparison_omegaTests
    {A X Z P A' X' Z' P' : C.{u, v}}
    (i : A ⟶ X) (a : A ⟶ Z) (x : X ⟶ P) (z : Z ⟶ P)
    (i' : A' ⟶ X') (a' : A' ⟶ Z') (x' : X' ⟶ P') (z' : Z' ⟶ P')
    (sq : IsPushout i a x z) (sq' : IsPushout i' a' x' z')
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hi' : PointedCGWH.EnrichedBasedHomotopyExtension.property i')
    (fA : A ⟶ A') (fX : X ⟶ X') (fZ : Z ⟶ Z') (fP : P ⟶ P')
    (hI : fA ≫ i' = i ≫ fX) (hA : fA ≫ a' = a ≫ fZ)
    (hX : fX ≫ x' = x ≫ fP) (hZ : fZ ≫ z' = z ≫ fP)
    (hfA : W fA) (hfX : W fX) (hfZ : W fZ) : W fP := by
  rw [omegaTests_eq_integerPiStar] at hfA hfX hfZ ⊢
  exact OriginalRawPiHomotopyPushoutGluing.originalRawPiHEPpushoutGluing
    i a x z i' a' x' z' sq sq' hi hi' fA fX fZ fP hI hA hX hZ hfA hfX hfZ

private def originalHEPOmega : MorphismProperty C.{u, v} :=
  PointedCGWH.EnrichedBasedHomotopyExtension.property ⊓ W

private instance originalHEPOmega_cobase : (originalHEPOmega (B := B)).IsStableUnderCobaseChange
  where
  of_isPushout sq hi :=
    ⟨MorphismProperty.of_isPushout sq hi.1,
      originalHEPPushout_omegaTests _ _ _ _ sq.flip hi.1 hi.2⟩

private instance originalHEPOmega_transfinite :
    (originalHEPOmega (B := B)).IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    unfold originalHEPOmega
    infer_instance

private instance originalHEPOmega_coproducts :
    (originalHEPOmega (B := B)).IsStableUnderCoproducts.{v} :=
  MorphismProperty.isStableUnderCoproducts_of_cobase_transfinite (originalHEPOmega (B := B))


end PointedCGWH.Spectra.OriginalCoefficientCells.Sequential

end SequentialHEPClosure07

section SequentialCoproductClosure08

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.EnrichedIntervalMappingCylinder
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells.Sequential

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev C4 := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev W4 := NativeK.omegaTests (B := B) originalFamily.{u, v}
private abbrev Q4 := Replacement.cofibrantReplacement (B := B)
  (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
private abbrev ε4 := Replacement.cofibrantReplacementCounit (B := B)
  (A := PointedCGWH.Spectra.Sequential.Index.{u, v})

private instance originalNativePointedColimits :
    HasColimitsOfSize.{v, v} PointedCGWH.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.Native.nativeColimits

private instance originalNativeCarrierColimits : HasColimitsOfSize.{v, v} C4.{u, v} := by
  change HasColimitsOfSize.{v, v}
    (EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v})
  infer_instance

omit B in
private theorem originalNativeHasCoproduct {J : Type v} (F : J → C4.{u, v}) :
    HasCoproduct F := by
  let _ : HasColimitsOfShape (Discrete J) C4.{u, v} :=
    @HasColimitsOfSize.has_colimits_of_shape C4.{u, v} _
      originalNativeCarrierColimits (Discrete J) _
  exact HasColimitsOfShape.has_colimit (Discrete.functor F)

attribute [local instance] originalNativeHasCoproduct

omit B in
private theorem originalNativeHasProducts (J : Type v) :
    HasProductsOfShape J PointedCGWH.{u, v} := by
  let h : HasLimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} := by infer_instance
    change HasLimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  exact @HasLimitsOfSize.has_limits_of_shape PointedCGWH.{u, v} _ h (Discrete J) _

attribute [local instance] originalNativeHasProducts

private theorem originalQMap_omegaTests {X Y : C4.{u, v}} (f : X ⟶ Y) (hf : W4 f) :
    W4 (Q4.map f) := by
  have hX : W4 (ε4.app X) := NativeK.levelWeak_le_omegaTests originalFamily _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X)
  have hY : W4 (ε4.app Y) := NativeK.levelWeak_le_omegaTests originalFamily _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences Y)
  have h := W4.comp_mem _ _ hX hf
  have hn : Q4.map f ≫ ε4.app Y = ε4.app X ≫ f := ε4.naturality f
  rw [← hn] at h
  exact W4.of_postcomp _ _ hY h

/-- The actual coproduct of all original sequential replacement counits is
Omega weak by the original HEP cylinder sources and the full coproduct SDR. -/
private theorem originalCoproductCounit_omegaTests {J : Type v} (X : J → C4.{u, v}) :
    W4 (Limits.Sigma.map (fun j => ε4.app (X j))) := by
  let f := fun j => Arrow.mk (ε4.app (X j))
  let i := fun j => source (f j)
  let r := fun j => retraction (f j)
  have hr (j : J) : W4 (r j) := NativeK.levelWeak_le_omegaTests originalFamily _
    ((HomotopicalAlgebra.weakEquivalence_iff _).mp
      (PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.retraction_weakEquivalence (f j)))
  have hi (j : J) : originalHEPOmega (B := B) (i j) := by
    refine ⟨PointedCGWH.EnrichedBasedHomotopyExtension.source_mem (f j), ?_⟩
    have hCounit : W4 (ε4.app (X j)) := NativeK.levelWeak_le_omegaTests originalFamily _
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (X j))
    have hFac : i j ≫ r j = ε4.app (X j) := fac (f j)
    exact W4.of_postcomp _ _ (hr j) (hFac.symm ▸ hCounit)
  have hSource : originalHEPOmega (B := B) (Limits.Sigma.map i) :=
    MorphismProperty.coproductMap_mem_of_cobase_transfinite (originalHEPOmega (B := B)) i hi
  have hRetraction : W4 (Limits.Sigma.map r) := NativeK.levelWeak_le_omegaTests originalFamily _
    (PointedCGWH.EnrichedIntervalMappingCylinder.Coproducts.sigmaRetraction_levelWeak
      (fun j => ε4.app (X j)))
  have hFac : Limits.Sigma.map i ≫ Limits.Sigma.map r =
      Limits.Sigma.map (fun j => ε4.app (X j)) := by
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_map,
      ← Category.assoc, fac, Sigma.ι_map]
    rfl
  exact hFac ▸ W4.comp_mem _ _ hSource.2 hRetraction

/-- Every possibly infinite wedge of original sequential stable weak arrows
is weak, with both original arbitrary endpoint families unchanged. -/
theorem originalCoproductMap_omegaTests {J : Type v}
    {X Y : J → C4.{u, v}} (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, W4 (f j)) :
    W4 (Limits.Sigma.map f) := by
  let fq := fun j => Q4.map (f j)
  let _ : ∀ j, IsCofibrant (Q4.obj (X j)) :=
    fun j => Replacement.isCofibrant_cofibrantReplacement (X j)
  let _ : ∀ j, IsCofibrant (Q4.obj (Y j)) :=
    fun j => Replacement.isCofibrant_cofibrantReplacement (Y j)
  have hfq : ∀ j, W4 (fq j) := fun j => originalQMap_omegaTests (f j) (hf j)
  have hQ : W4 (Limits.Sigma.map fq) := StableCoproductClosure.omegaTests_sigmaMap originalFamily
    fq hfq
  have hX : W4 (Limits.Sigma.map (fun j => ε4.app (X j))) := originalCoproductCounit_omegaTests X
  have hY : W4 (Limits.Sigma.map (fun j => ε4.app (Y j))) := originalCoproductCounit_omegaTests Y
  have hNat : Limits.Sigma.map fq ≫ Limits.Sigma.map (fun j => ε4.app (Y j)) =
      Limits.Sigma.map (fun j => ε4.app (X j)) ≫ Limits.Sigma.map f := by
    rw [Sigma.map_comp_map, Sigma.map_comp_map]
    apply congrArg (fun g : ∀ j, Q4.obj (X j) ⟶ Y j => Limits.Sigma.map g)
    funext j
    exact ε4.naturality (f j)
  exact W4.of_precomp _ _ hX (hNat ▸ W4.comp_mem _ _ hQ hY)

theorem originalOmegaCoproducts : W4.{u, v}.IsStableUnderCoproducts.{v} :=
  { isStableUnderCoproductsOfShape := fun J =>
      MorphismProperty.IsStableUnderCoproductsOfShape.mk _ J
        (fun _ _ _ _ f hf => originalCoproductMap_omegaTests f hf) }


end PointedCGWH.Spectra.OriginalCoefficientCells.Sequential

end SequentialCoproductClosure08

section OriginalStableWeakClosures15

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells.Closure

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit B in
private theorem nativeHasCoproduct {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
    {J : Type v} (X : J → EnrichedFunctorCat PointedCGWH.{u, v} I) : HasCoproduct X := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.nativeColimits
  let h : HasColimitsOfSize.{v, v} (EnrichedFunctorCat PointedCGWH.{u, v} I) := by infer_instance
  let _ : HasColimitsOfShape (Discrete J) (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
    @HasColimitsOfSize.has_colimits_of_shape (EnrichedFunctorCat PointedCGWH.{u, v} I) _ h
      (Discrete J) _
  exact HasColimitsOfShape.has_colimit (Discrete.functor X)

attribute [local instance] nativeHasCoproduct

private abbrev sequentialWeak : MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  (StableModelConstruction.sequentialModelCategory.{u, v} (B :=
    B)).categoryWithWeakEquivalences.weakEquivalences

private theorem sequentialWeak_eq : sequentialWeak = NativeK.omegaTests (B := B)
  Sequential.originalFamily.{u, v} := by
  let _ : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
    StableModelConstruction.sequentialModelCategory (B := B)
  exact (StableModelConstruction.sequential_five_classes (B := B)).1

/-- Every original sequential wedge retains both caller endpoint families and all weak maps. -/
theorem sequentialCoproduct_weak {J : Type v} {X Y : J → PointedCGWH.SequentialSpectrum.{u, v}}
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, sequentialWeak (f j)) : sequentialWeak (Limits.Sigma.map f)
      := by
  rw [sequentialWeak_eq] at hf ⊢
  exact PointedCGWH.Spectra.OriginalCoefficientCells.Sequential.originalCoproductMap_omegaTests f hf

/-- The same original sequential HEP weak arrow remains weak on the caller's exact pushout. -/
theorem sequentialHEPPushout_weak
    {A X Z P : PointedCGWH.SequentialSpectrum.{u, v}} (i : A ⟶ X) (a : A ⟶ Z) (x : X ⟶ P) (z : Z
      ⟶ P)
    (sq : IsPushout i a x z) (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hf : sequentialWeak i) : sequentialWeak z := by
  rw [sequentialWeak_eq] at hf ⊢
  exact PointedCGWH.Spectra.OriginalCoefficientCells.Sequential.originalHEPPushout_omegaTests i a
    x z sq hi hf

/-- All three original vertical sequential maps and both caller pushout squares are retained. -/
theorem sequentialHEPPushoutComparison_weak
    {A X Z P A' X' Z' P' : PointedCGWH.SequentialSpectrum.{u, v}}
    (i : A ⟶ X) (a : A ⟶ Z) (x : X ⟶ P) (z : Z ⟶ P)
    (i' : A' ⟶ X') (a' : A' ⟶ Z') (x' : X' ⟶ P') (z' : Z' ⟶ P')
    (sq : IsPushout i a x z) (sq' : IsPushout i' a' x' z')
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hi' : PointedCGWH.EnrichedBasedHomotopyExtension.property i')
    (fA : A ⟶ A') (fX : X ⟶ X') (fZ : Z ⟶ Z') (fP : P ⟶ P')
    (hI : fA ≫ i' = i ≫ fX) (hA : fA ≫ a' = a ≫ fZ)
    (hX : fX ≫ x' = x ≫ fP) (hZ : fZ ≫ z' = z ≫ fP)
    (hfA : sequentialWeak fA) (hfX : sequentialWeak fX) (hfZ : sequentialWeak fZ) :
      sequentialWeak fP := by
  rw [sequentialWeak_eq] at hfA hfX hfZ ⊢
  exact Sequential.originalHEPPushoutComparison_omegaTests
    i a x z i' a' x' z' sq sq' hi hi' fA fX fZ fP hI hA hX hZ hfA hfX hfZ

/-- Every original HEP weak sequence retains its actual sequential initial-to-colimit map. -/
theorem sequentialHEPOrdinal_weak
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (F : J ⥤ PointedCGWH.SequentialSpectrum.{u, v}) [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hW : ∀ j, ¬IsMax j → sequentialWeak (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) : sequentialWeak (c.ι.app ⊥) := by
  rw [sequentialWeak_eq] at hW ⊢
  exact OriginalOmegaMappingOrdinalClosure.originalHEPOrdinal_small_omegaTests
    Sequential.originalFamily F hF hW c hc

/-- Every original vertical sequential ordinal comparison keeps both cocones and all leg
  equations. -/
theorem sequentialHEPOrdinalComparison_weak
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (F G : J ⥤ PointedCGWH.SequentialSpectrum.{u, v}) [F.IsWellOrderContinuous]
      [G.IsWellOrderContinuous]
    (α : F ⟶ G)
    (hF : ∀ j, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hG : ∀ j, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (G.map (homOfLE (Order.le_succ j))))
    (hα : ∀ j, sequentialWeak (α.app j))
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (f : c.pt ⟶ d.pt) (hf : ∀ j, c.ι.app j ≫ f = α.app j ≫ d.ι.app j) : sequentialWeak f := by
  rw [sequentialWeak_eq] at hα ⊢
  exact StableHEPOrdinalWeakComparison.originalHEPOrdinalSmallComparison_omegaTests
    Sequential.originalFamily F G α hF hG hα c d hc hd f hf

private abbrev symmetricWeak : MorphismProperty Actual.SymmetricCarrier.{u, v} :=
  (StableModelConstruction.symmetricModelCategory.{u, v} (B :=
    B)).categoryWithWeakEquivalences.weakEquivalences

private theorem symmetricWeak_eq : symmetricWeak = NativeK.omegaTests (B := B)
  Actual.symmetricFamily.{u, v} := by
  let _ : ModelCategory Actual.SymmetricCarrier.{u, v} :=
    StableModelConstruction.symmetricModelCategory (B := B)
  exact (StableModelConstruction.symmetric_five_classes (B := B)).1

/-- Every original symmetric wedge retains both caller endpoint families and all weak maps. -/
theorem symmetricCoproduct_weak {J : Type v} {X Y : J → Actual.SymmetricCarrier.{u, v}}
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, symmetricWeak (f j)) : symmetricWeak (Limits.Sigma.map f) := by
  rw [symmetricWeak_eq] at hf ⊢
  exact PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure.originalCoproductMap_omegaTests f hf

/-- The same original symmetric HEP weak arrow remains weak on the caller's exact pushout. -/
theorem symmetricHEPPushout_weak
    {A X Z P : Actual.SymmetricCarrier.{u, v}} (i : A ⟶ X) (a : A ⟶ Z) (x : X ⟶ P) (z : Z ⟶ P)
    (sq : IsPushout i a x z) (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hf : symmetricWeak i) : symmetricWeak z := by
  rw [symmetricWeak_eq] at hf ⊢
  exact PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure.originalHEPPushout_omegaTests i a x
    z sq hi hf

/-- All three original vertical symmetric maps and both caller pushout squares are retained. -/
theorem symmetricHEPPushoutComparison_weak
    {A X Z P A' X' Z' P' : Actual.SymmetricCarrier.{u, v}}
    (i : A ⟶ X) (a : A ⟶ Z) (x : X ⟶ P) (z : Z ⟶ P)
    (i' : A' ⟶ X') (a' : A' ⟶ Z') (x' : X' ⟶ P') (z' : Z' ⟶ P')
    (sq : IsPushout i a x z) (sq' : IsPushout i' a' x' z')
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hi' : PointedCGWH.EnrichedBasedHomotopyExtension.property i')
    (fA : A ⟶ A') (fX : X ⟶ X') (fZ : Z ⟶ Z') (fP : P ⟶ P')
    (hI : fA ≫ i' = i ≫ fX) (hA : fA ≫ a' = a ≫ fZ)
    (hX : fX ≫ x' = x ≫ fP) (hZ : fZ ≫ z' = z ≫ fP)
    (hfA : symmetricWeak fA) (hfX : symmetricWeak fX) (hfZ : symmetricWeak fZ) : symmetricWeak fP
      := by
  rw [symmetricWeak_eq] at hfA hfX hfZ ⊢
  exact Symmetric.OriginalHEPOmegaClosure.originalHEPPushoutComparison_omegaTests
    i a x z i' a' x' z' sq sq' hi hi' fA fX fZ fP hI hA hX hZ hfA hfX hfZ

/-- Every original HEP weak sequence retains its actual symmetric initial-to-colimit map. -/
theorem symmetricHEPOrdinal_weak
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (F : J ⥤ Actual.SymmetricCarrier.{u, v}) [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hW : ∀ j, ¬IsMax j → symmetricWeak (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) : symmetricWeak (c.ι.app ⊥) := by
  rw [symmetricWeak_eq] at hW ⊢
  exact OriginalOmegaMappingOrdinalClosure.originalHEPOrdinal_small_omegaTests
    Actual.symmetricFamily F hF hW c hc

/-- Every original vertical symmetric ordinal comparison keeps both cocones and all leg
  equations. -/
theorem symmetricHEPOrdinalComparison_weak
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (F G : J ⥤ Actual.SymmetricCarrier.{u, v}) [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    (α : F ⟶ G)
    (hF : ∀ j, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hG : ∀ j, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (G.map (homOfLE (Order.le_succ j))))
    (hα : ∀ j, symmetricWeak (α.app j))
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (f : c.pt ⟶ d.pt) (hf : ∀ j, c.ι.app j ≫ f = α.app j ≫ d.ι.app j) : symmetricWeak f := by
  rw [symmetricWeak_eq] at hα ⊢
  exact StableHEPOrdinalWeakComparison.originalHEPOrdinalSmallComparison_omegaTests
    Actual.symmetricFamily F G α hF hG hα c d hc hd f hf

private abbrev orthogonalWeak : MorphismProperty Actual.OrthogonalCarrier.{u, v} :=
  (StableModelConstruction.orthogonalModelCategory.{u, v} (B :=
    B)).categoryWithWeakEquivalences.weakEquivalences

private theorem orthogonalWeak_eq : orthogonalWeak = NativeK.omegaTests (B := B)
  Actual.orthogonalFamily.{u, v} := by
  let _ : ModelCategory Actual.OrthogonalCarrier.{u, v} :=
    StableModelConstruction.orthogonalModelCategory (B := B)
  exact (StableModelConstruction.orthogonal_five_classes (B := B)).1

/-- Every original orthogonal wedge retains both caller endpoint families and all weak maps. -/
theorem orthogonalCoproduct_weak {J : Type v} {X Y : J → Actual.OrthogonalCarrier.{u, v}}
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, orthogonalWeak (f j)) : orthogonalWeak (Limits.Sigma.map f)
      := by
  rw [orthogonalWeak_eq] at hf ⊢
  exact PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure.originalCoproductMap_omegaTests f hf

/-- The same original orthogonal HEP weak arrow remains weak on the caller's exact pushout. -/
theorem orthogonalHEPPushout_weak
    {A X Z P : Actual.OrthogonalCarrier.{u, v}} (i : A ⟶ X) (a : A ⟶ Z) (x : X ⟶ P) (z : Z ⟶ P)
    (sq : IsPushout i a x z) (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hf : orthogonalWeak i) : orthogonalWeak z := by
  rw [orthogonalWeak_eq] at hf ⊢
  exact PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure.originalHEPPushout_omegaTests i a
    x z sq hi hf

/-- All three original vertical orthogonal maps and both caller pushout squares are retained. -/
theorem orthogonalHEPPushoutComparison_weak
    {A X Z P A' X' Z' P' : Actual.OrthogonalCarrier.{u, v}}
    (i : A ⟶ X) (a : A ⟶ Z) (x : X ⟶ P) (z : Z ⟶ P)
    (i' : A' ⟶ X') (a' : A' ⟶ Z') (x' : X' ⟶ P') (z' : Z' ⟶ P')
    (sq : IsPushout i a x z) (sq' : IsPushout i' a' x' z')
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hi' : PointedCGWH.EnrichedBasedHomotopyExtension.property i')
    (fA : A ⟶ A') (fX : X ⟶ X') (fZ : Z ⟶ Z') (fP : P ⟶ P')
    (hI : fA ≫ i' = i ≫ fX) (hA : fA ≫ a' = a ≫ fZ)
    (hX : fX ≫ x' = x ≫ fP) (hZ : fZ ≫ z' = z ≫ fP)
    (hfA : orthogonalWeak fA) (hfX : orthogonalWeak fX) (hfZ : orthogonalWeak fZ) :
      orthogonalWeak fP := by
  rw [orthogonalWeak_eq] at hfA hfX hfZ ⊢
  exact Orthogonal.OriginalHEPOmegaClosure.originalHEPPushoutComparison_omegaTests
    i a x z i' a' x' z' sq sq' hi hi' fA fX fZ fP hI hA hX hZ hfA hfX hfZ

/-- Every original HEP weak sequence retains its actual orthogonal initial-to-colimit map. -/
theorem orthogonalHEPOrdinal_weak
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (F : J ⥤ Actual.OrthogonalCarrier.{u, v}) [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hW : ∀ j, ¬IsMax j → orthogonalWeak (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) : orthogonalWeak (c.ι.app ⊥) := by
  rw [orthogonalWeak_eq] at hW ⊢
  exact OriginalOmegaMappingOrdinalClosure.originalHEPOrdinal_small_omegaTests
    Actual.orthogonalFamily F hF hW c hc

/-- Every original vertical orthogonal ordinal comparison keeps both cocones and all leg
  equations. -/
theorem orthogonalHEPOrdinalComparison_weak
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (F G : J ⥤ Actual.OrthogonalCarrier.{u, v}) [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    (α : F ⟶ G)
    (hF : ∀ j, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hG : ∀ j, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (G.map (homOfLE (Order.le_succ j))))
    (hα : ∀ j, orthogonalWeak (α.app j))
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (f : c.pt ⟶ d.pt) (hf : ∀ j, c.ι.app j ≫ f = α.app j ≫ d.ι.app j) : orthogonalWeak f := by
  rw [orthogonalWeak_eq] at hα ⊢
  exact StableHEPOrdinalWeakComparison.originalHEPOrdinalSmallComparison_omegaTests
    Actual.orthogonalFamily F G α hF hG hα c d hc hd f hf


end PointedCGWH.Spectra.OriginalCoefficientCells.Closure

end OriginalStableWeakClosures15
