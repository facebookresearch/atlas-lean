/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeOmegaTransferModels
public import MathlibExt.AlgebraicGeometry.NativeBetaModuleDerivedModels
public import MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus

/-!
# Native D-module duality from regular D, inverse top-form transfer and dimension

The right dual is actual RHom_D(M,D), retaining regular D's right action.
The r-conversion is the actual Omega tensor regular-D transfer. Its native
right adjoint supplies inverse r; invertibility/unit/counit proofs are
separate ordinary line-module requests. The original [dim X] shift is
applied in native derived modules. Native alpha/right-beta projection
returns the actual ordinary D-module dual.

Source: DK1311.2374v2 Section2.5 and Definition9.1.1;
Mathlib56a005 native regular module, tensor/Hom, adjoints and shifts, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeDModuleDualityModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeBetaModuleDerivedModels
open NativeOmegaTransferModels HolomorphicCotangentModuleModels
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
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
  [CompactSheafSource ℂ (TopCat.of X)] [IndSpaceSource (TopCat.of X)]
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
attribute [local instance] HasDerivedCategory.standard

variable (Omega : OmegaTransferSource n X)
  [LeftTensorDerivationSource (Rop n X) (R n X) (U X)]
  [LeftTensorHomSource (Rop n X) (R n X) (U X)]

abbrev nativeRFunctor : DerivedCategory (Bimod (R n X) (U X)) ⥤
    DerivedCategory (Bimod (Rop n X) (U X)) :=
  (tensorDerivedLeft (Rop n X) (R n X) (U X)).obj
    ((DerivedCategory.singleFunctor (Bimod (Rop n X) (R n X)) 0).obj (nativeOmegaTransfer n X Omega))

def nativeRInverse : DerivedCategory (Bimod (Rop n X) (U X)) ⥤
    DerivedCategory (Bimod (R n X) (U X)) :=
  letI : (nativeRFunctor n X Omega).IsLeftAdjoint :=
    LeftTensorHomSource.closed (R := Rop n X) (S := R n X) (T := U X)
      ((DerivedCategory.singleFunctor (Bimod (Rop n X) (R n X)) 0).obj (nativeOmegaTransfer n X Omega))
  (nativeRFunctor n X Omega).rightAdjoint

/-- The chosen inverse top-form conversion is tied to its original tensor-Hom adjunction. -/
def nativeRAdjunction : nativeRFunctor n X Omega ⊣ nativeRInverse n X Omega :=
  letI : (nativeRFunctor n X Omega).IsLeftAdjoint :=
    LeftTensorHomSource.closed (R := Rop n X) (S := R n X) (T := U X)
      ((DerivedCategory.singleFunctor (Bimod (Rop n X) (R n X)) 0).obj
        (nativeOmegaTransfer n X Omega))
  Adjunction.ofIsLeftAdjoint (nativeRFunctor n X Omega)

variable [LeftTensorDerivationSource (R n X) (U X) (R n X)]
  [LeftTensorHomSource (R n X) (U X) (R n X)]
  (RO : OppositeMonoidSource (R n X) (Rop n X)) (UO : OppositeMonoidSource (U X) (U X))
  (RightOpposite : OppositeBimoduleSource (U X) (R n X) (U X) (Rop n X) UO RO)
  [RightOpposite.functor.Additive] (OppExact : ExactImageSource RightOpposite.functor)

def nativeDualIndObject (M : DerivedCategory (Bimod (R n X) (U X))) :
    DerivedCategory (Bimod (R n X) (U X)) :=
  let rightDual := ((homLeftDerived (R n X) (U X) (R n X)).obj (Opposite.op M)).obj
    ((DerivedCategory.singleFunctor (Bimod (R n X) (R n X)) 0).obj (Bimod.regular (R n X)))
  (shiftFunctor (DerivedCategory (Bimod (R n X) (U X))) (n : ℤ)).obj
    ((nativeRInverse n X Omega).obj ((derivedExactImage RightOpposite.functor OppExact).obj rightDual))

/-- The native duality functor retains the contravariant module-Hom maps and source dimension shift. -/
def nativeDualIndFunctor : (DerivedCategory (Bimod (R n X) (U X)))ᵒᵖ ⥤
    DerivedCategory (Bimod (R n X) (U X)) :=
  homLeftDerived (R n X) (U X) (R n X) ⋙
    (_root_.CategoryTheory.evaluation (DerivedCategory (Bimod (R n X) (R n X)))
      (DerivedCategory (Bimod (U X) (R n X)))).obj
        ((DerivedCategory.singleFunctor (Bimod (R n X) (R n X)) 0).obj (Bimod.regular (R n X))) ⋙
    derivedExactImage RightOpposite.functor OppExact ⋙ nativeRInverse n X Omega ⋙
      shiftFunctor (DerivedCategory (Bimod (R n X) (U X))) (n : ℤ)

variable (Ordinary : OrdinaryBetaModuleSource (TopCat.of X) (analyticDifferentialRing n X))
  (Normalize : BetaUnitNormalizationSource (TopCat.of X) (analyticDifferentialRing n X))
  [(betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize).Additive]
  (BetaExact : ExactImageSource
    (betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize))
  [(derivedBetaModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize BetaExact).IsLeftAdjoint]

def ordinaryDualObject (M : DerivedCategory
    (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X) (analyticDifferentialRing n X))) :
    DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) :=
  (derivedBetaModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize BetaExact).rightAdjoint.obj
    (nativeDualIndObject n X Omega RO UO RightOpposite OppExact
      ((derivedBetaModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize BetaExact).obj M))

def ordinaryDualFunctor :
    (DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)))ᵒᵖ ⥤
      DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
        (analyticDifferentialRing n X)) :=
  (derivedBetaModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize BetaExact).op ⋙
    nativeDualIndFunctor n X Omega RO UO RightOpposite OppExact ⋙
      (derivedBetaModules (TopCat.of X) (analyticDifferentialRing n X)
        Ordinary Normalize BetaExact).rightAdjoint

end MathlibExt.AlgebraicGeometry.NativeDModuleDualityModels
