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

public import MathlibExt.KTheory.Milnor.ClassicalSymbols
public import MathlibExt.KTheory.Milnor.K2Powers
public import MathlibExt.KTheory.Milnor.K2Symmetry

/-!
# Classical K₂ laws for `MilnorK F 2`

Multiplication, inverse, division, power, and anticommutativity laws for
`k2Symbol` in `MilnorK F 2`. `MilnorK F 2` is definitionally
`MilnorKRing.degree F 2`, so these are direct corollaries of the
`MilnorKRing` K₂ API in `K2`, `K2Powers`, and `K2Symmetry`.

## Main results
* `k2Symbol_mul_left`, `k2Symbol_mul_right`
* `k2Symbol_inv_left`, `k2Symbol_inv_right`
* `k2Symbol_div_left`, `k2Symbol_div_right`
* `k2Symbol_pow_left`, `k2Symbol_pow_right`, `k2Symbol_zpow_left`, `k2Symbol_zpow_right`
* `k2Symbol_pow_pow`, `k2Symbol_zpow_zpow`
* `k2Symbol_a_a`, `k2Symbol_add_swap`, `k2Symbol_anticomm`
-/

@[expose] public section

namespace MilnorK

variable (F : Type*) [Field F]

/-- Left multiplication: `{(a * b), c} = {a, c} + {b, c}` in `MilnorK F 2`. -/
theorem k2Symbol_mul_left (a b c : Fˣ) :
    k2Symbol F (a * b) c = k2Symbol F a c + k2Symbol F b c := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_mul_left a b c

/-- Right multiplication: `{a, b * c} = {a, b} + {a, c}` in `MilnorK F 2`. -/
theorem k2Symbol_mul_right (a b c : Fˣ) :
    k2Symbol F a (b * c) = k2Symbol F a b + k2Symbol F a c := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_mul_right a b c

/-- Integer power in the left slot: `{(a ^ z), b} = z • {a, b}`. -/
theorem k2Symbol_zpow_left (a b : Fˣ) (n : ℤ) :
    k2Symbol F (a ^ n) b = n • k2Symbol F a b := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_zpow_left a b n

/-- Integer power in the right slot: `{a, b ^ z} = z • {a, b}`. -/
theorem k2Symbol_zpow_right (a b : Fˣ) (n : ℤ) :
    k2Symbol F a (b ^ n) = n • k2Symbol F a b := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_zpow_right a b n

/-- Natural power in the left slot: `{(a ^ n), b} = n • {a, b}`. -/
theorem k2Symbol_pow_left (a b : Fˣ) (n : ℕ) :
    k2Symbol F (a ^ n) b = n • k2Symbol F a b := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_pow_left a b n

/-- Natural power in the right slot: `{a, b ^ n} = n • {a, b}`. -/
theorem k2Symbol_pow_right (a b : Fˣ) (n : ℕ) :
    k2Symbol F a (b ^ n) = n • k2Symbol F a b := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_pow_right a b n

/-- Left inverse: `{a⁻¹, b} = - {a, b}` in `MilnorK F 2`. -/
theorem k2Symbol_inv_left (a b : Fˣ) :
    k2Symbol F a⁻¹ b = - k2Symbol F a b := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_inv_left a b

/-- Right inverse: `{a, b⁻¹} = - {a, b}` in `MilnorK F 2`. -/
theorem k2Symbol_inv_right (a b : Fˣ) :
    k2Symbol F a b⁻¹ = - k2Symbol F a b := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_inv_right a b

/-- Left division: `{a / b, c} = {a, c} - {b, c}` in `MilnorK F 2`. -/
theorem k2Symbol_div_left (a b c : Fˣ) :
    k2Symbol F (a / b) c = k2Symbol F a c - k2Symbol F b c := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_div_left a b c

/-- Right division: `{a, b / c} = {a, b} - {a, c}` in `MilnorK F 2`. -/
theorem k2Symbol_div_right (a b c : Fˣ) :
    k2Symbol F a (b / c) = k2Symbol F a b - k2Symbol F a c := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_div_right a b c

/-- Natural powers in both slots: `{(a ^ m), b ^ n} = (m * n) • {a, b}`. -/
theorem k2Symbol_pow_pow (a b : Fˣ) (m n : ℕ) :
    k2Symbol F (a ^ m) (b ^ n) = (m * n) • k2Symbol F a b := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_pow_pow a b m n

/-- Integer powers in both slots: `{(a ^ m), b ^ n} = (m * n) • {a, b}` for `ℤ`. -/
theorem k2Symbol_zpow_zpow (a b : Fˣ) (m n : ℤ) :
    k2Symbol F (a ^ m) (b ^ n) = (m * n) • k2Symbol F a b := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_zpow_zpow a b m n

/-- Self-symbol reduction: `{a, a} = {a, -1}` in `MilnorK F 2`. -/
theorem k2Symbol_a_a (a : Fˣ) :
    k2Symbol F a a = k2Symbol F a (-1 : Fˣ) := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_a_a a

/-- Symmetric-sum vanishing: `{a, b} + {b, a} = 0` in `MilnorK F 2`. -/
theorem k2Symbol_add_swap (a b : Fˣ) :
    k2Symbol F a b + k2Symbol F b a = 0 := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_add_swap a b

/-- Anticommutativity: `{a, b} = - {b, a}` in `MilnorK F 2`. -/
theorem k2Symbol_anticomm (a b : Fˣ) :
    k2Symbol F a b = - k2Symbol F b a := by
  apply Subtype.ext
  exact MilnorKRing.k2Symbol_anticomm a b

end MilnorK
