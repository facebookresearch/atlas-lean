/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RealCoefficientPerverseSheaves
public import MathlibExt.AlgebraicGeometry.RightDifferentialModules

@[expose] public section

/-!
# Tests for real-coefficient sheaves and right differential modules

The embedding of a real subfield into `ℂ` is the inclusion and is fixed by
conjugation. Extension of coefficients to `ℂ` is the coefficient-generic scalar
extension, hence exact. The right action reverses products of operators.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open MathlibExt.AlgebraicGeometry
open RealCoefficientPerverseSheaves MathlibExt.Algebra.RealSubfieldCoefficients

namespace MathlibExtTest.AlgebraicGeometry.RealCoefficientPerverseSheaves

attribute [local instance] complexAlgebra

variable (A : Subfield ℝ)

example (a : A) : complexEmbedding A a = ((a : ℝ) : ℂ) := complexEmbedding_apply A a

example (a : A) : star (complexEmbedding A a) = complexEmbedding A a :=
  complexEmbedding_star A a

example (a : A) : algebraMap A ℂ a = ((a : ℝ) : ℂ) := rfl

example (Z : TopCat.{0}) :
    extendCoefficients A Z = ConstructibleComplexes.scalarExtension A ℂ Z := rfl

example (Z : TopCat.{0}) : PreservesFiniteLimits (extendCoefficients A Z) := inferInstance

example (Z : TopCat.{0}) : PreservesFiniteColimits (extendCoefficients A Z) := inferInstance

end MathlibExtTest.AlgebraicGeometry.RealCoefficientPerverseSheaves

namespace MathlibExtTest.AlgebraicGeometry.RightDifferentialModules

open Opposite MathlibExt.AlgebraicGeometry.RightDifferentialModules
open MathlibExt.AlgebraicGeometry.DifferentialOperatorSheaves

variable (k : Type) [CommRing k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]

/-- Right modules: acting by `P * Q` is acting by `P`, then by `Q`. -/
example (N : RightModule k M O) (U : Opens M) (P Q : finiteOperatorRing k M O U)
    (s : N.val.obj (op U)) :
    rightAct k M O N U (P * Q) s = rightAct k M O N U Q (rightAct k M O N U P s) :=
  rightAct_mul k M O N U P Q s

end MathlibExtTest.AlgebraicGeometry.RightDifferentialModules
