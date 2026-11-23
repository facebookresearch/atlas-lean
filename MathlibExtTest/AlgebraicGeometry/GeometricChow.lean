/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricChow

@[expose] public section

/-! # Tests for `MathlibExt.AlgebraicGeometry.GeometricChow` -/

noncomputable section

open AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricChow

namespace MathlibExtTest.AlgebraicGeometry.GeometricChow

/-- The dimension grading is `Order.height` for the specialization order:
closed points have height zero. -/
example (X : Scheme.{0}) (x : X) (hx : IsClosed {x}) : Order.height x = 0 :=
  Scheme.height_of_isClosed hx

/-- The generic point of an irreducible scheme has coheight (codimension)
zero: every point is a specialization of it. -/
example (X : Scheme.{0}) [IrreducibleSpace X] : Order.coheight (genericPoint X) = 0 := by
  rw [Order.coheight_eq_zero]
  intro y _
  rw [Scheme.le_iff_specializes]
  exact (genericPoint_spec X).specializes (Set.mem_univ y)

/-- Rational cycles carry the pointwise rational action. -/
example (X : Scheme.{0}) (a : ℚ) (c : AlgebraicCycle X ℚ) (x : X) : (a • c) x = a * c x :=
  rfl

/-- The zero cycle has every dimension. -/
example (X : Scheme.{0}) (r : ℕ) : (0 : AlgebraicCycle X ℚ) ∈ cyclesOfDimension X r :=
  zero_mem _

/-- Every defining flat-family relation vanishes in the Chow group. -/
example (X : ComplexScheme) (r : ℕ) (F : FlatFamily X r) :
    (rationalEquivalences X r).mkQ F.difference = 0 :=
  family_difference_zero X r F

end MathlibExtTest.AlgebraicGeometry.GeometricChow

end
