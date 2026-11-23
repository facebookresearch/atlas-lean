/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpaceRelativePulledCoverComparison

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology Opposite
open scoped Simplicial

universe u

#check TopCat.HSpaceCommonUnitFibration.originalRelativeChainDiagram_eq
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeChainDiagram_eq
#check TopCat.HSpaceCommonUnitFibration.originalPulledInclusion_integralHomology_isIso
#print axioms TopCat.HSpaceCommonUnitFibration.originalPulledInclusion_integralHomology_isIso

namespace HSpaceRelativePulledCoverComparisonTests

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (x : X) (n : ℕ) :
    IsIso (SSet.homologyMap
      (SSet.KanComplex.nativeCoverBaseChangeMap
        (TopCat.HSpaceCommonUnitFibration.relativeInclusion f)
        (TopCat.HSpaceCommonUnitFibration.relativeInclusion_projection f)
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x)))
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) :=
  TopCat.HSpaceCommonUnitFibration.originalPulledInclusion_integralHomology_isIso f h x n

end HSpaceRelativePulledCoverComparisonTests
