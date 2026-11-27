/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeDModuleDualityModels
public import MathlibExt.AlgebraicGeometry.NativeOrdinaryDifferentialRepresentations
public import MathlibExt.AlgebraicGeometry.IndSheafDerivedAlphaModels
public import MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
public import MathlibExt.AlgebraicGeometry.OrdinaryIndDerivedModels
public import MathlibExt.AlgebraicGeometry.RegularHolonomicModels

/-!
# Actual ordinary DR and Sol before enhancement

O is the original full-operator structure module mapped by left beta.
Omega is the actual top-form regular-D transfer tensored with O, with
its original right D action. DR is balanced Omega tensor and Sol is the
native contravariant left-D module Hom into O. Coefficient forgetting
and actual derived alpha return ordinary complex sheaves. No comparison
object or final solution functor is supplied independently. The right
view of Omega depends on the opposite structure `RBack`; comparisons with
classical de Rham complexes require it to be the canonical
anti-identification (`CanonicalOppositeRings.IsCanonicalBack`).

Source: DK1311.2374v2 Section2.5 and Definition9.1.1;
Mathlib56a005 native tensor/Hom, beta/alpha and Q, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeOrdinaryDRSolModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeBetaModuleDerivedModels
open NativeOmegaTransferModels HolomorphicCotangentModuleModels
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open NativeOrdinaryDifferentialRepresentations IndSheafDerivedAlphaModels
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open scoped Manifold ContDiff

variable (n : ℕ) (X : Type) [TopologicalSpace X]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X]
  [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [CotangentSectionCalculus (n := n) (M := X)] [CotangentSheafCondition (n := n) (M := X)]
  [HasSheafify (Opens.grothendieckTopology X) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ (TopCat.of X)] [CX : IndSpaceSource (TopCat.of X)]
  [DifferentialBetaSource X (analyticCoefficients n X)]
  [OppositeDifferentialBetaSource X (analyticCoefficients n X)]

abbrev R := betaRing (TopCat.of X) (analyticDifferentialRing n X)
abbrev Rop := betaRing (TopCat.of X) (analyticOppositeDifferentialRing n X)
abbrev U := Mon.trivial (IndSheaf ℂ (TopCat.of X))

local instance dualityPreadditive (A B : Mon (IndSheaf ℂ (TopCat.of X))) :
    Preadditive (Bimod A B) := Abelian.toPreadditive
local instance ordinaryDualityPreadditive :
    Preadditive (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) := Abelian.toPreadditive
local instance ordinaryScalarIndPreadditive : Preadditive (IndSheaf ℂ (TopCat.of X)) :=
  Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard


variable (Ordinary : OrdinaryBetaModuleSource (TopCat.of X) (analyticDifferentialRing n X))
  (Normalize : BetaUnitNormalizationSource (TopCat.of X) (analyticDifferentialRing n X))
  [(betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize).Additive]
  (BetaExact : ExactImageSource
    (betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize))
  (Structure : StructureModuleSource X (analyticCoefficients n X))

def actualOrdinaryO : DerivedCategory (Bimod (R n X) (U X)) :=
  (DerivedCategory.singleFunctor (Bimod (R n X) (U X)) 0).obj
    ((betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize).obj
      Structure.object)

variable (Omega : OmegaTransferSource n X)
  [LeftTensorDerivationSource (Rop n X) (R n X) (U X)]
  (RBack : OppositeMonoidSource (Rop n X) (R n X))
  (UnitOpp : OppositeMonoidSource (U X) (U X))
  (RightView : OppositeBimoduleSource (Rop n X) (U X) (R n X) (U X) RBack UnitOpp)
  [RightView.functor.Additive] (RightExact : ExactImageSource RightView.functor)

def actualOrdinaryOmega : DerivedCategory (Bimod (U X) (R n X)) :=
  (derivedExactImage RightView.functor RightExact).obj
    (((tensorDerivedLeft (Rop n X) (R n X) (U X)).obj
      ((DerivedCategory.singleFunctor (Bimod (Rop n X) (R n X)) 0).obj
        (nativeOmegaTransfer n X Omega))).obj
          (actualOrdinaryO n X Ordinary Normalize Structure))

variable [(Bimod.forget (B := U X) (U X)).Additive]
  (CoefficientExact : ExactCoefficientSource (U X) (U X))
  [(IndSheafAlphaBetaModels.alpha ℂ (TopCat.of X) CX.alpha).Additive]
  (AlphaExact : ExactAlphaSource ℂ (TopCat.of X) CX.alpha)

abbrev ordinaryCoefficientProjection : DerivedCategory (Bimod (U X) (U X)) ⥤
    OrdinaryDerived ℂ (TopCat.of X) :=
  derivedCoefficients (U X) (U X) CoefficientExact ⋙
    derivedAlpha ℂ (TopCat.of X) CX.alpha AlphaExact

variable [LeftTensorDerivationSource (U X) (R n X) (U X)]

/-- Actual covariant ordinary de Rham through the original right-D top forms. -/
def actualOrdinaryDR :
    DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) ⥤ OrdinaryDerived ℂ (TopCat.of X) :=
  derivedBetaModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize BetaExact ⋙
    (tensorDerivedLeft (U X) (R n X) (U X)).obj
      (actualOrdinaryOmega n X Ordinary Normalize Structure Omega RBack UnitOpp RightView RightExact) ⋙
    ordinaryCoefficientProjection X CoefficientExact AlphaExact

section Regular

variable [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{0}]
  [∀ V : Opens X,
    ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (V : Opens X) (W : Over V), HasWeakSheafify
    (((Opens.grothendieckTopology X).over V).over W) AddCommGrpCat.{0}]
  [∀ (V : Opens X) (W : Over V),
    (((Opens.grothendieckTopology X).over V).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]
  (RegularBounded : ∀ L : RegularHolonomicModels.RegularHolonomicDerived n X,
    IsBoundedDerived (OrdinarySheaf ℂ (TopCat.of X))
      ((actualOrdinaryDR n X Ordinary Normalize BetaExact Structure Omega
        RBack UnitOpp RightView RightExact CoefficientExact AlphaExact).obj L.obj))

/-- The actual ordinary DR restricted to arbitrary-support bounded regular holonomic complexes. -/
def actualRegularOrdinaryDR : RegularHolonomicModels.RegularHolonomicDerived n X ⥤
    OrdinaryIndDerivedModels.BoundedOrdinary ℂ (TopCat.of X) :=
  (IsBoundedDerived (OrdinarySheaf ℂ (TopCat.of X))).lift
    ((RegularHolonomicModels.IsBoundedRegularHolonomic n X).ι ⋙
      actualOrdinaryDR n X Ordinary Normalize BetaExact Structure Omega
        RBack UnitOpp RightView RightExact CoefficientExact AlphaExact) RegularBounded

end Regular

variable [LeftTensorDerivationSource (R n X) (U X) (U X)]
  [LeftTensorHomSource (R n X) (U X) (U X)]

/-- Actual contravariant ordinary solutions through full left-D module Hom into O. -/
def actualOrdinarySol :
    (DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)))ᵒᵖ ⥤ OrdinaryDerived ℂ (TopCat.of X) :=
  (derivedBetaModules (TopCat.of X) (analyticDifferentialRing n X)
    Ordinary Normalize BetaExact).op ⋙ homLeftDerived (R n X) (U X) (U X) ⋙
    (_root_.CategoryTheory.evaluation (DerivedCategory (Bimod (R n X) (U X)))
      (DerivedCategory (Bimod (U X) (U X)))).obj
        (actualOrdinaryO n X Ordinary Normalize Structure) ⋙
    ordinaryCoefficientProjection X CoefficientExact AlphaExact

end MathlibExt.AlgebraicGeometry.NativeOrdinaryDRSolModels
