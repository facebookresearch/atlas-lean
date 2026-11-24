/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.TotalComplexSymmetry

@[expose] public section

open CategoryTheory

namespace HomologicalComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance : TotalComplexShapeSymmetry (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  symm p q := add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro _ p rfl q
    dsimp
    rw [mul_one, add_mul, one_mul, pow_add, mul_comm]
  σ_ε₂ := by
    rintro p _ q rfl
    dsimp
    rw [one_mul, mul_add, mul_one, pow_add, mul_assoc,
      Int.units_mul_self, mul_one]

@[simp] theorem ComplexShape.σ_down_ℕ (p q : ℕ) :
    ComplexShape.σ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) p q = (-1 : ℤˣ) ^ (p * q) :=
  rfl

instance : TotalComplexShapeSymmetrySymmetry (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  σ_symm p q := by
    rw [ComplexShape.σ_down_ℕ, ComplexShape.σ_down_ℕ, Nat.mul_comm q p]

end HomologicalComplex
