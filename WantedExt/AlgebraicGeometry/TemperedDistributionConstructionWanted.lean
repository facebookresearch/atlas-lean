/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ManifoldDistributionModels
public import MathlibExt.AlgebraicGeometry.TemperedDolbeaultCoordinateModels
public import MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves

/-!
# Structural LF, coordinate and Dolbeault construction requests

Every requested proof refers to the already prescribed actual chart
image, test-density Jacobian, restriction or signed partial-zbar operator.
Source: DK arXiv:1311.2374v2, Sections 5.1--5.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.TemperedDistributionConstructionWanted

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry
open scoped Manifold ContDiff
open MathlibExt.AlgebraicGeometry.TemperedDistributionSectionModels
open MathlibExt.AlgebraicGeometry.TemperedDolbeaultCoordinateModels
open MathlibExt.AlgebraicGeometry.ManifoldDistributionModels

theorem_wanted actual_native_derivative_restriction (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : DerivativeRestrictionSource E

theorem_wanted actual_dolbeault_square_zero (n : ℕ)
    (S : DerivativeRestrictionSource (TemperedDistributionSectionModels.ComplexCoordinates n))
    (U : TopologicalSpace.Opens (TemperedDistributionSectionModels.ComplexCoordinates n)) :
  DolbeaultSquareZeroSource n S U

def_wanted actual_distribution_chart_opens (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M] :
  ChartOpenSource n M

def_wanted actual_test_density_transfer (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
    [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
    (O : ChartOpenSource n M) : TestDensityTransferSource n M O

theorem_wanted actual_distribution_sheaf_gluing (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
    [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
    (O : ChartOpenSource n M) (J : TestDensityTransferSource n M O) :
  DistributionSheafSource n M O J

end WantedExt.AlgebraicGeometry.TemperedDistributionConstructionWanted
