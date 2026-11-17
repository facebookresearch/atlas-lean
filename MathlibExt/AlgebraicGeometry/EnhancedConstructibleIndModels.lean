/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EnhancedStableCoefficientModels
public import MathlibExt.AlgebraicGeometry.RealSubanalyticConstructibleModels
public import MathlibExt.AlgebraicGeometry.OrdinaryIndDerivedModels
public import MathlibExt.AlgebraicGeometry.EnhancedSheafHomModels
public import MathlibExt.AlgebraicGeometry.SubanalyticIndDistributionModels
public import MathlibExt.AlgebraicGeometry.BorderedRealConstructibleModels

/-!
# Actual bordered and enhanced R-constructibility

The ordinary source is the actual M times R. Its actual ordinary Rj!
must be constructible on M times the compactified real line, including
both reciprocal boundary charts and local finiteness at infinity.
Bordered Ind realization is actual Rj! after the prescribed ordinary
iota embedding. Enhanced constructibility is precisely local
stabilization by the actual closed-half-line Ind colimit and the original
real convolution formula, on every relatively compact subanalytic U.

Source: DK1311.2374v2 Definitions4.9.1,4.9.2;
Mathlib56a005 native filtered colimits, iota, proper image and Q, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EnhancedConstructibleIndModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels BoundedIndOperationSources
open EnhancedIndQuotientModels BorderedIndDerivedModels EnhancedConvolutionModels
open EnhancedStableCoefficientModels EnhancedSheafHomModels
open RealSubanalyticConstructibleModels OrdinaryIndDerivedModels SubanalyticIndDistributionModels
open BorderedRealSpaceModels BorderedRealTimeModels BorderedGraphKernelModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]

abbrev RealInterior := TopCat.of (M × ℝ)

def finiteRealInclusion : RealInterior M ⟶ (enhancedSpace (TopCat.of M)).ambient :=
  BorderedRealConstructibleModels.finiteRealInclusion M

variable [CompactSheafSource ℂ (TopCat.of M)]
  [CompactSheafSource ℂ (RealInterior M)]
  [CompactSheafSource ℂ (enhancedSpace (TopCat.of M)).ambient]
  [CompactSheafSource ℂ (boundarySpace (enhancedSpace (TopCat.of M)))]

local instance constructibleIndPreadditive (X : TopCat.{0}) [CompactSheafSource ℂ X] :
    Preadditive (IndSheaf ℂ X) := Abelian.toPreadditive
local instance constructibleOrdinaryPreadditive :
    Preadditive (OrdinarySheaf ℂ (RealInterior M)) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (Iota : OrdinaryIndSource ℂ (RealInterior M))
  [(ordinaryToInd ℂ (RealInterior M) Iota).Additive]
  (IotaExact : ExactImageSource (ordinaryToInd ℂ (RealInterior M) Iota))
  (IotaBounded : BoundedIotaSource ℂ (RealInterior M) Iota IotaExact)
  (J : ProperSource ℂ (finiteRealInclusion M))
  [(BorderedRealConstructibleModels.ordinaryCompactifiedExtension M).Additive]
  (OrdinaryExtensionExact : ExactImageSource
    (BorderedRealConstructibleModels.ordinaryCompactifiedExtension M))

/-- Exact bordered realization uses the actual finite-real inclusion, without a stalk support kernel. -/
def ordinaryBorderedRealization :
    BoundedOrdinary ℂ (RealInterior M) ⥤ BoundedIndDerived ℂ (enhancedSpace (TopCat.of M)).ambient :=
  boundedIota ℂ (RealInterior M) Iota IotaExact IotaBounded ⋙
    properFunctor ℂ (finiteRealInclusion M) J

variable (B : ProperSource ℂ (boundaryInclusion (enhancedSpace (TopCat.of M))))
  (P : InverseSource ℂ (baseProjection (TopCat.of M)))
  (R : EnhancedRepresentativeSource ℂ (TopCat.of M) B P)
  (Tensor : TensorSource ℂ (enhancedSpace (TopCat.of M)).ambient)
  (Closed : ClosedHalfLineDiagramSource (TopCat.of M))
  (StableIota : OrdinaryIndSource ℂ (enhancedSpace (TopCat.of M)).ambient)
  (Colimit : StableColimitSource (TopCat.of M) Closed StableIota)
  (C : CompactOpenCoefficientSource n M)

structure ConstructibleSingleSource : Prop where
  stableBounded : IsBounded ℂ (enhancedSpace (TopCat.of M)).ambient
    ((DerivedCategory.singleFunctor (IndSheaf ℂ (enhancedSpace (TopCat.of M)).ambient) 0).obj
      (stableIndCoefficient (TopCat.of M) Closed StableIota Colimit))
  probeBounded : ∀ U : RelativelyCompactSubanalyticOpen n M,
    IsBounded ℂ (TopCat.of M)
      ((DerivedCategory.singleFunctor (IndSheaf ℂ (TopCat.of M)) 0).obj (openProbe n M C U))

variable (S : ConstructibleSingleSource n M Closed StableIota Colimit C)

def stableBounded : BoundedIndDerived ℂ (enhancedSpace (TopCat.of M)).ambient :=
  ⟨(DerivedCategory.singleFunctor (IndSheaf ℂ (enhancedSpace (TopCat.of M)).ambient) 0).obj
    (stableIndCoefficient (TopCat.of M) Closed StableIota Colimit), S.stableBounded⟩

def localScalarCut (U : RelativelyCompactSubanalyticOpen n M)
    (K : EnhancedCategory ℂ (TopCat.of M) B P) : EnhancedCategory ℂ (TopCat.of M) B P :=
  (enhancedSourceProjection ℂ (TopCat.of M) B P).obj
    (((tensorFunctor ℂ (enhancedSpace (TopCat.of M)).ambient Tensor).obj
      ((inverseFunctor ℂ (baseProjection (TopCat.of M)) P).obj
        ⟨(DerivedCategory.singleFunctor (IndSheaf ℂ (TopCat.of M)) 0).obj (openProbe n M C U),
          S.probeBounded U⟩)).obj
            ((rightRepresentative ℂ (TopCat.of M) B P R).obj K))

variable
  [CompactSheafSource ℂ (doubleTimeSpace (TopCat.of M)).ambient]
  [CompactSheafSource ℂ (sumProduct (TopCat.of M))]
  (G : TimeSumGraphSource (TopCat.of M))
  (SumTensor : TensorSource ℂ (sumProduct (TopCat.of M)))
  (SumInverse : InverseSource ℂ (firstProjection (doubleTimeSpace (TopCat.of M))
    (enhancedSpace (TopCat.of M))))
  (SumProper : ProperSource ℂ (secondProjection (doubleTimeSpace (TopCat.of M))
    (enhancedSpace (TopCat.of M))))
  (TimeTensor : TensorSource ℂ (doubleTimeSpace (TopCat.of M)).ambient)
  (First : InverseSource ℂ (timeFirst (TopCat.of M)))
  (Second : InverseSource ℂ (timeSecond (TopCat.of M)))

/-- Definition4.9.2, retaining the actual Rj! ordinary source and stable real-parameter convolution. -/
def IsEnhancedRConstructible (K : EnhancedCategory ℂ (TopCat.of M) B P) : Prop :=
  ∀ U : RelativelyCompactSubanalyticOpen n M,
    ∃ F : BorderedRealConstructibleModels.BorderedRConstructibleDerived M OrdinaryExtensionExact
        (TemperedDistributionSectionModels.ComplexCoordinates n),
      Nonempty (localScalarCut n M B P R Tensor Closed StableIota Colimit C S U K ≅
        (((convolutionBeforeQuotient ℂ (TopCat.of M) B P G SumTensor SumInverse SumProper
          TimeTensor First Second).obj (stableBounded n M Closed StableIota Colimit C S)).obj
            ((ordinaryBorderedRealization M Iota IotaExact IotaBounded J).obj F.obj)))

end MathlibExt.AlgebraicGeometry.EnhancedConstructibleIndModels
