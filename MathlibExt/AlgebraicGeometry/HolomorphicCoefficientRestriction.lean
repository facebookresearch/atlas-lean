/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts

/-!
# Holomorphic functions as coefficients of analytic D-modules

The sheaf of holomorphic functions maps to the coefficient sheaf of the analytic differential
operators by the sheafification unit of the holomorphic ring presheaf. Restricting scalars along
this map views every analytic D-module as a module over the holomorphic functions. This is the one
restriction used by the holonomic characteristic-support models and by the holomorphic coefficient
modules.

Source: DK1311.2374v2 Sections 2.5 and 9.1. Native sheaf modules and restriction of scalars:
Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HolomorphicCoefficientRestriction

open _root_.CategoryTheory TopologicalSpace
open NativeIndDifferentialContexts HarmonicHolomorphicModuleModels
open scoped Manifold ContDiff

variable (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]

/-- The sheafification unit from the holomorphic functions to the coefficient sheaf of the analytic
differential operators. -/
def holomorphicCoefficientMap : holomorphicStructureRing (n := n) (M := M) ⟶
    DifferentialOperatorScalars.coefficientSheaf ℂ M (analyticCoefficients n M) :=
  ObjectProperty.homMk (toSheafify (Opens.grothendieckTopology M)
    (HolomorphicCoefficientSheaves.ringPresheaf
      (TemperedDistributionSectionModels.ComplexCoordinates n) M))

variable [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- An analytic D-module viewed as a module over the holomorphic functions. -/
def holomorphicRestriction
    (N : DifferentialOperatorSheaves.DModule ℂ M (analyticCoefficients n M)) :
    SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M)) :=
  (SheafOfModules.restrictScalars (holomorphicCoefficientMap n M)).obj
    ((DifferentialOperatorScalars.underlyingO ℂ M (analyticCoefficients n M)).obj N)

end MathlibExt.AlgebraicGeometry.HolomorphicCoefficientRestriction
