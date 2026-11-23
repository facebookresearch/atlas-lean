/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpaceRelativeLowestRow

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology

universe u

#check TopCat.HSpaceCommonUnitFibration.originalRelativeChainDiagram
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeChainDiagram
#check TopCat.HSpaceCommonUnitFibration.originalRelativeCoefficientHomologyZero_isZero_of_lower_coefficients
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeCoefficientHomologyZero_isZero_of_lower_coefficients
#check TopCat.HSpaceCommonUnitFibration.originalRelativeCoefficientHomologyZero_zero_isZero
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeCoefficientHomologyZero_zero_isZero
#check TopCat.HSpaceCommonUnitFibration.originalRelativeHomologyCoefficients_map_isIso
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeHomologyCoefficients_map_isIso
#check TopCat.HSpaceCommonUnitFibration.originalRelativeRootAction
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeRootAction
#check TopCat.HSpaceCommonUnitFibration.originalRelativeRootCoinvariants_subsingleton_of_lower_coefficients
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeRootCoinvariants_subsingleton_of_lower_coefficients

namespace HSpaceRelativeLowestRowTests

open TopCat.HSpaceCommonUnitFibration

variable {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
  [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
  (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))

example (q : ℕ) (hBelow : ∀ k : ℕ, k < q → ∀ s,
    IsZero (((originalRelativeChainDiagram f).obj s).homology k)) :
    IsZero (homologyWithCoefficients (originalRelativeChainDiagram f ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) q) 0) :=
  originalRelativeCoefficientHomologyZero_isZero_of_lower_coefficients f h q hBelow

example : IsZero (homologyWithCoefficients (originalRelativeChainDiagram f ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 0) 0) :=
  originalRelativeCoefficientHomologyZero_zero_isZero f h

example (q : ℕ) (i : SSet.SimplexIndex
    (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))
    (hBelow : ∀ k : ℕ, k < q → ∀ s,
      IsZero (((originalRelativeChainDiagram f).obj s).homology k)) :
    Subsingleton (Representation.Coinvariants (originalRelativeRootAction f q i)) :=
  originalRelativeRootCoinvariants_subsingleton_of_lower_coefficients f h q i hBelow

end HSpaceRelativeLowestRowTests

#check TopCat.HSpaceCommonUnitFibration.originalRelativeRootAction_ker_le_invariants
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeRootAction_ker_le_invariants
#check TopCat.HSpaceCommonUnitFibration.originalRelativeRootAction_augmentationDifference_fixed
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeRootAction_augmentationDifference_fixed
#check TopCat.HSpaceCommonUnitFibration.originalRelativeHomologyCoefficients_isZero_of_integralHomology_isIso
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeHomologyCoefficients_isZero_of_integralHomology_isIso
#check SSet.simplexPullbackDiagramMap_mono
#print axioms SSet.simplexPullbackDiagramMap_mono
#check SSet.relativeSimplexChainArrow_mono
#print axioms SSet.relativeSimplexChainArrow_mono

namespace OriginalHSpaceRelativeNilpotenceTests

open TopCat.HSpaceCommonUnitFibration

variable {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
  [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
  (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f))
  (q : ℕ) (i : SSet.SimplexIndex
    (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))

example : Representation.Coinvariants.ker (originalRelativeRootAction f q i) ≤
    (originalRelativeRootAction f q i).invariants :=
  originalRelativeRootAction_ker_le_invariants f h1 q i

example (g h : End ((SSet.categoryNerveUnit (SSet.SimplexIndex
    (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))))).obj i))
    (v : ((originalRelativeChainDiagram f).obj i).homology q) :
    originalRelativeRootAction f q i g (originalRelativeRootAction f q i h v - v) =
      originalRelativeRootAction f q i h v - v :=
  originalRelativeRootAction_augmentationDifference_fixed f h1 q i g h v

example
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f)) :
    IsZero (((originalRelativeChainDiagram f).obj i).homology q) :=
  originalRelativeHomologyCoefficients_isZero_of_integralHomology_isIso f h q i

end OriginalHSpaceRelativeNilpotenceTests
