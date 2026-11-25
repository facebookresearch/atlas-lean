/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.Basic

/-!
# Elementary Milnor symbol relations

Inverse and division laws for the degree-one Milnor symbol.
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable {F : Type*} [Field F]

/-- Inverse law for the degree-one symbol. -/
@[simp]
theorem symbol_inv (a : Fˣ) : symbol F a⁻¹ = - symbol F a := by
  have h : symbol F a⁻¹ + symbol F a = 0 := by
    rw [← symbol_mul F a⁻¹ a, inv_mul_cancel, symbol_one]
  exact eq_neg_iff_add_eq_zero.mpr h

/-- Division law for the degree-one symbol. -/
@[simp]
theorem symbol_div (a b : Fˣ) : symbol F (a / b) = symbol F a - symbol F b := by
  rw [div_eq_mul_inv, symbol_mul, symbol_inv, sub_eq_add_neg]

end MilnorKRing
end MilnorK
