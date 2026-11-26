/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RightVFiltrationModels
public import MathlibExt.AlgebraicGeometry.RightDifferentialCoefficientModels
public import MathlibExt.AlgebraicGeometry.CoefficientPerverseModels
public import MathlibExt.AlgebraicGeometry.RightHodgeSourceRequestsActualGradedEulerLocalNilpotence
public import MathlibExt.AlgebraicGeometry.RightHodgeSourceRequestsActualNearbyEulerComposition

/-!
# Shared source requests for actual right-D and coefficient-perverse primitives

The objects, original differential operators, rational V pieces and
native cokernel maps are fixed by the public source. These requests
construct their normalized coefficient and graded operators and prove
their literal Euler identities; the local nilpotence of the graded Euler
operators is proved in
`MathlibExt.AlgebraicGeometry.RightHodgeSourceRequestsActualGradedEulerLocalNilpotence`.
The nearby Euler composition `actual_nearby_euler_composition` is proved in
`MathlibExt.AlgebraicGeometry.RightHodgeSourceRequestsActualNearbyEulerComposition`.
They do not assert regular holonomicity,
graded polarizability or local mixed-Hodge admissibility.

Source: Saito1307.2140v5, Sections1.1--1.5,2.1,2.2 and2.4;
the coefficient-perverse source locators remain in CoefficientPerverseModels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RightHodgeSourceRequests

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.RightDifferentialModules
open MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials
open MathlibExt.AlgebraicGeometry.RightVFiltrationModels
open MathlibExt.AlgebraicGeometry.RightDifferentialCoefficientModels
open MathlibExt.AlgebraicGeometry.CoefficientPerverseModels

/-- The coefficient middle t-structure is constructed on the actual complex variety and supports. -/
def_wanted actual_coefficient_perverse_theory (k : Type) [Field k]
    (X : MathlibExt.AlgebraicGeometry.PerverseSheaves.ComplexScheme)
    [MathlibExt.AlgebraicGeometry.PerverseSheaves.IsComplexVariety X] :
    CoefficientPerverseTheory k X

/-- An actual natural finite-order right operator has its coefficient-linear sheaf realization. -/
def_wanted actual_right_coefficient_operator (k : Type) [CommRing k]
    (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    (P : NaturalOperator k M O) (N : RightModule k M O) : CoefficientOperator k M O P N

variable (k : Type) [CommRing k] [Algebra ℚ k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens M, HasWeakSheafify ((Opens.grothendieckTopology M).over U) AddCommGrpCat.{0}]
  [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  (C : CoordinateDerivation k M O) (N : RightModule k M O)
  (V : RationalVFiltration k M O C N)

/-- The original t, partial and right Euler actions descend to their actual native V-cokernels. -/
def_wanted actual_right_graded_v_operators : GradedVOperators k M O C N V

/-- The actual Weyl relation identifies vanishing var-can with partial*t-1. -/
theorem_wanted actual_vanishing_euler_composition (A : GradedVOperators k M O C N V) :
    vanishingNilpotent k M O C N V A = A.eulerMap (-1)

end WantedExt.AlgebraicGeometry.RightHodgeSourceRequests
