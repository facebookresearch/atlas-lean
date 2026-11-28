/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.ImaginaryQuadraticOrderUnits
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

@[expose] public section

/-! Tests for `MathlibExt.NumberTheory.NumberField.ImaginaryQuadraticOrderUnits`. -/

namespace NumberField.IsOrder.ImaginaryQuadraticOrderUnitsTest

#check @NumberField.IsOrder.natCard_units_integralClosure
#check @NumberField.IsOrder.natCard_units_of_ne
#check @NumberField.IsOrder.index_units_range

instance : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  CyclotomicField.isCyclotomicExtension 4 ℚ

/-- The Gaussian field `ℚ(i)`, as the fourth cyclotomic field, is imaginary quadratic. -/
theorem finrank_cyclotomicField_four : Module.finrank ℚ (CyclotomicField 4 ℚ) = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 4 (CyclotomicField 4 ℚ)]
  decide

instance : NumberField.IsTotallyComplex (CyclotomicField 4 ℚ) :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) (CyclotomicField 4 ℚ) (by norm_num)

-- The ring of integers of `ℚ(i)` has `2`, `4` or `6` units.
example : Nat.card (integralClosure ℤ (CyclotomicField 4 ℚ))ˣ = 2 ∨
    Nat.card (integralClosure ℤ (CyclotomicField 4 ℚ))ˣ = 4 ∨
      Nat.card (integralClosure ℤ (CyclotomicField 4 ℚ))ˣ = 6 :=
  NumberField.IsOrder.natCard_units_integralClosure finrank_cyclotomicField_four

-- For the maximal order of `ℚ(i)` the unit index is `1`.
example (hO : NumberField.IsOrder (CyclotomicField 4 ℚ)
      (integralClosure ℤ (CyclotomicField 4 ℚ))) :
    (Units.map (MonoidHom.ofClass
      (Subalgebra.inclusion hO.le_integralClosure))).range.index = 1 :=
  (NumberField.IsOrder.index_units_range hO finrank_cyclotomicField_four).2.1 rfl

-- The maximal order is an order, so the previous example applies to it.
example : NumberField.IsOrder (CyclotomicField 4 ℚ) (integralClosure ℤ (CyclotomicField 4 ℚ)) :=
  NumberField.isOrder_integralClosure _

-- A non-maximal order of `ℚ(i)` has exactly the units `±1`.
example (O : Subalgebra ℤ (CyclotomicField 4 ℚ)) (hO : NumberField.IsOrder _ O)
    (hne : O ≠ integralClosure ℤ (CyclotomicField 4 ℚ)) : Nat.card Oˣ = 2 :=
  NumberField.IsOrder.natCard_units_of_ne hO finrank_cyclotomicField_four hne

end NumberField.IsOrder.ImaginaryQuadraticOrderUnitsTest

end
