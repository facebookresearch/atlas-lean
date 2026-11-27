/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeDModuleDualityModels
public import MathlibExt.AlgebraicGeometry.HolonomicCharacteristicSupportModels

/-!
# Source top-form conversion and actual native duality requests

The unit and counit belong to the actual Omega tensor/native module-Hom
adjunction. Ordinary duality is the computed native regular-D Hom,
inverse r, dimension shift and original beta/alpha module projection.
Requests are structural and source statements, with no replacement
objects or reconstruction map fields.
Source: DK1311.2374v2 Section2.5/Definition9.1.1; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NativeDModuleDualityWanted

open MathlibExt.AlgebraicGeometry
open NativeDModuleDualityModels

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

local instance dualityPreadditive (A B : Mon (IndSheaf ℂ (TopCat.of X))) :
    Preadditive (Bimod A B) := Abelian.toPreadditive
local instance ordinaryDualityPreadditive :
    Preadditive (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (Omega : OmegaTransferSource n X)
  [LeftTensorDerivationSource (Rop n X) (R n X) (U X)]
  [LeftTensorHomSource (Rop n X) (R n X) (U X)]


theorem_wanted actual_topform_r_unit_isIso (M : DerivedCategory (Bimod (R n X) (U X))) :
  IsIso ((nativeRAdjunction n X Omega).unit.app M)

theorem_wanted actual_topform_r_counit_isIso (M : DerivedCategory (Bimod (Rop n X) (U X))) :
  IsIso ((nativeRAdjunction n X Omega).counit.app M)

end WantedExt.AlgebraicGeometry.NativeDModuleDualityWanted
