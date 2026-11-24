/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.Convolution
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Action.Defs

/-!
# The actual nonunital Haar twisted convolution algebra

The multiplication is the original Haar integral convolution on Carrier μ α.
Its additive group and complex module are the original data from Basic.
Associativity, distributivity, zero multiplication and scalar compatibility
are constructed from the same literal convolution laws. These are the
algebraic data needed by the original universal C-star gauge.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

/-- Multiplication is exactly the original Haar twisted convolution. -/
instance instMulCarrier : Mul (Carrier μ α) :=
  ⟨convolution μ α⟩

/-- The original indexed compact-support carrier has its genuine nonunital convolution ring. -/
instance instNonUnitalRingCarrier : NonUnitalRing (Carrier μ α) where
  __ := instAddCommGroupCarrier μ α
  __ := instMulCarrier μ α
  mul_assoc := convolution_assoc μ α
  left_distrib := convolution_add_right μ α
  right_distrib := convolution_add_left μ α
  zero_mul := convolution_zero_left μ α
  mul_zero := convolution_zero_right μ α

/-- Complex scaling of the first source function commutes with actual convolution multiplication. -/
instance instIsScalarTowerCarrier : IsScalarTower ℂ (Carrier μ α) (Carrier μ α) where
  smul_assoc c f g := convolution_smul_left μ α c f g

/-- Complex scaling of the second source function commutes with actual convolution multiplication. -/
instance instSMulCommClassCarrier : SMulCommClass ℂ (Carrier μ α) (Carrier μ α) where
  smul_comm c f g := (convolution_smul_right μ α c f g).symm

end

end HaarTwistedCore
