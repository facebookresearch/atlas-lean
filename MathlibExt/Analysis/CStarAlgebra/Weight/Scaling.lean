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

public import MathlibExt.Analysis.CStarAlgebra.Weight
public import Mathlib.Algebra.Group.Action.Units

/-!
# Scalar multiplication of the original global weights

Finite nonnegative scalars multiply the original extended-positive weight
values. The weight carrier and its canonical positive cone belong to the
same possibly nonunital C-star algebra. The constructor laws give the
actual scalar monoid action; the standard unit-action API restricts it to
the positive finite-real group.

No weight support, normal/semifinite restriction, equivalence quotient,
continuous part, modular action or flow is selected or identified here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The actual global weight obtained by multiplying every original positive value by `r`. -/
def Weight.scale (r : NNReal) (φ : Weight A) : Weight A where
  value a := (r : ENNReal) * φ.value a
  zero_value := by
    rw [φ.zero_value, mul_zero]
  add_value a b := by
    rw [φ.add_value, mul_add]
  smul_value t a := by
    rw [φ.smul_value]
    exact mul_left_comm (r : ENNReal) (t : ENNReal) (φ.value a)

/-- Scalar multiplication keeps the literal original extended-positive values. -/
@[simp]
theorem Weight.scale_value (r : NNReal) (φ : Weight A) (a : PositiveElement A) :
    (Weight.scale r φ).value a = (r : ENNReal) * φ.value a :=
  rfl

/-- The scalar identity fixes the same original global weight. -/
theorem Weight.scale_one (φ : Weight A) : Weight.scale 1 φ = φ := by
  apply Weight.ext_value
  intro a
  rw [Weight.scale_value, ENNReal.coe_one, one_mul]

/-- Multiplication of finite nonnegative parameters is composition of the actual weight maps. -/
theorem Weight.scale_mul (r t : NNReal) (φ : Weight A) :
    Weight.scale (r * t) φ = Weight.scale r (Weight.scale t φ) := by
  apply Weight.ext_value
  intro a
  rw [Weight.scale_value, Weight.scale_value, Weight.scale_value, ENNReal.coe_mul, mul_assoc]

/-- The original scalar maps form their actual monoid action on global weights. -/
instance instMulActionWeight : MulAction NNReal (Weight A) where
  smul := Weight.scale
  one_smul := Weight.scale_one
  mul_smul := Weight.scale_mul

/-- The standard positive-real unit action uses literal multiplication of original weight values. -/
theorem Weight.units_smul_value (r : NNRealˣ) (φ : Weight A) (a : PositiveElement A) :
    (r • φ).value a = ((r : NNReal) : ENNReal) * φ.value a :=
  rfl

end

end CStarAlgebra.ScalarWeight
