/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ClassicalLoopQuotientModels
import Mathlib.Basic.Complex.Basic

/-! The original complex algebra tests include the zero algebra.
Positive-loop translations and twisted-product multiplication retain
the literal original group laws; no finite flag model is substituted.
-/

open CategoryTheory Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ClassicalLoopCoefficientTests
open MathlibExt.AlgebraicGeometry.ClassicalLoopQuotientModels

noncomputable section

private def zeroScalars : ℂ →+* PUnit where
  toFun _ := PUnit.unit
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private instance : Algebra ℂ PUnit := zeroScalars.toAlgebra

private def zeroTest : CommAlgCat.{0} ℂ := CommAlgCat.of ℂ PUnit

private theorem zeroPositive : Subsingleton (PositiveRing ℂ zeroTest) := by
  refine ⟨fun x y ↦ ?_⟩
  apply PowerSeries.ext
  intro n
  change (PowerSeries.coeff n x : PUnit) = (PowerSeries.coeff n y : PUnit)
  exact Subsingleton.elim _ _

example : Subsingleton (LoopRing ℂ zeroTest) := by
  have hz : (0 : PositiveRing ℂ zeroTest) = 1 := zeroPositive.elim _ _
  have hm := congrArg (algebraMap (PositiveRing ℂ zeroTest) (LoopRing ℂ zeroTest)) hz
  rw [map_zero, map_one] at hm
  exact subsingleton_of_zero_eq_one hm

variable (B : Type) [CommRing B] (G : Over (Spec (.of B))) [GrpObj G]

example (R : CommAlgCat.{0} B) (g : (loopSets B G).obj R)
    (h : (positiveSets B G).obj R) :
    (quotient B G).app R (g * (inclusion B G).app R h) = (quotient B G).app R g :=
  quotient_translate B G R g h

example : convolutionAction B G ≫ productToGrassmannian B G =
    convolutionProjection B G ≫ productToGrassmannian B G := multiplication_invariant B G

#print axioms
  MathlibExt.AlgebraicGeometry.ClassicalLoopCoefficientTests.loopRingMap_coefficients
#print axioms MathlibExt.AlgebraicGeometry.ClassicalLoopCoefficientTests.loopTests
#print axioms MathlibExt.AlgebraicGeometry.ClassicalLoopQuotientModels.grassmannian
#print axioms MathlibExt.AlgebraicGeometry.ClassicalLoopQuotientModels.convolutionMap
#print axioms MathlibExt.AlgebraicGeometry.ClassicalLoopQuotientModels.multiplication_invariant
