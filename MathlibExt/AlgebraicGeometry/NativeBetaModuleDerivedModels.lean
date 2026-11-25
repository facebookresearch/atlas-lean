/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts
public import MathlibExt.CategoryTheory.NativeMappedUnitMonoids
public import MathlibExt.CategoryTheory.NativeBimoduleScalarRestriction
public import MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

/-!
# Actual beta on ordinary native ring modules and its derived localization

Every ordinary carrier/action enters through the prescribed native beta
mapping. The coefficient ring is normalized by the same native mapMon
unit. Exact cochain localization retains all original ordinary objects
and maps. This is the source beta-pull input for enhanced DR and Sol.

Source: DK1311.2374v2 Sections2.2,4.10,9.1;
Mathlib56a005 native mapMon, unit, module maps and Q, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeBetaModuleDerivedModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts RingedComplexCoefficientModels
open MathlibExt.CategoryTheory.NativeMappedUnitMonoids
open MathlibExt.CategoryTheory.NativeBimoduleScalarRestriction
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

variable (X : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X] [CX : IndSpaceSource X]
  (R : TopCat.Sheaf RingCat.{0} X) [BetaRingSource X R]
  (N : OrdinaryBetaModuleSource X R)

abbrev UnitRing := Mon.trivial (IndSheaf ℂ X)

def betaUnitComparison : coefficientMonoid X ≅ UnitRing X :=
  mappedUnitIso (IndSheafAlphaBetaModels.beta ℂ X CX.alpha CX.beta)

structure BetaUnitNormalizationSource where
  restriction : ScalarRestrictionSource (betaRing X R) (coefficientMonoid X)
    (betaRing X R) (UnitRing X) (𝟙 _) (betaUnitComparison X).inv

def betaUnitModules (S : BetaUnitNormalizationSource X R) :
    OrdinaryModule X R ⥤ Bimod (betaRing X R) (UnitRing X) :=
  betaModules X R N ⋙ S.restriction.functor

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]

local instance ordinaryBetaPreadditive : Preadditive (OrdinaryModule X R) := Abelian.toPreadditive
local instance indBetaPreadditive : Preadditive (Bimod (betaRing X R) (UnitRing X)) :=
  Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (S : BetaUnitNormalizationSource X R) [(betaUnitModules X R N S).Additive]
  (E : ExactImageSource (betaUnitModules X R N S))

def derivedBetaModules : DerivedCategory (OrdinaryModule X R) ⥤
    DerivedCategory (Bimod (betaRing X R) (UnitRing X)) :=
  derivedExactImage (betaUnitModules X R N S) E

end MathlibExt.AlgebraicGeometry.NativeBetaModuleDerivedModels
