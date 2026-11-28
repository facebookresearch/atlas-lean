/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.DoubleRounding
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Floor
public meta import CSLibExt.Algorithms.Lean.Numerical.DoubleRounding
public meta import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Data.Rat.Floor

/-!
# Tests for double rounding through an extended precision

Executed fixtures over `ℚ`:
* The x87 example: `1 + 2^(-53) + 2^(-78)` rounds directly to `1 + 2^(-52)` at 53 bits, but at
  64 bits to the tie `1 + 2^(-53)`, which 53 bits round to `1`.
* The counterexamples at the boundary precisions for `p = 4` (Figueroa's, in Roux's Remarks 11,
  21 and 30), and those of the general families: the sum and quotient families for
  `p = 2, 3, 5, 8` and the product family for `p = 5, 6, 9`.
* Exhaustively for `p = 3`, all pairs of floats with significands below `8` in absolute value and
  exponents in `[-3, 3]`, zero included (so `x / 0 = 0` is exercised too): double rounding
  through `p' = 7` bits is innocuous for `+` and `-`, and through `p' = 6` bits for `×` and `/`.
* Gradual underflow, exhaustively for `p = 2`, `q = 0`, `q' = -4`, all pairs of format numbers
  with exponents in `[0, 4]`, zero included: double rounding through `flIn 5 (-4)` for `+` and
  `-`, and through `flIn 4 (-4)` for `×` and `/`, is innocuous; with `q' = q = 0` the quotient
  `16 / 3` is a counterexample.

Closed checks instantiate the theorems for binary64 and binary32.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint

private meta def check (label : String) (actual expected : ℚ) : IO Unit := do
  unless actual == expected do throw (IO.userError s!"{label}: got {actual}, expected {expected}")
  IO.println s!"{label}: {actual}"

/-! The x87 example -/

#eval check "x87, direct" (fl 53 (1 + (2 ^ (-53 : ℤ) + 2 ^ (-78 : ℤ)) : ℚ)) (1 + 2 ^ (-52 : ℤ))
#eval check "x87, 64 bits" (fl 64 (1 + (2 ^ (-53 : ℤ) + 2 ^ (-78 : ℤ)) : ℚ)) (1 + 2 ^ (-53 : ℤ))
#eval check "x87, through 64 bits" (fl 53 (fl 64 (1 + (2 ^ (-53 : ℤ) + 2 ^ (-78 : ℤ)) : ℚ))) 1

/-! Counterexamples at the boundary precisions -/

/-- `fl p (fl p' z)` and `fl p z` must differ. -/
private meta def checkDiffers (label : String) (p p' : ℕ) (z : ℚ) : IO Unit := do
  let a := fl p (fl p' z)
  let b := fl p z
  if a == b then throw (IO.userError s!"{label}: double rounding of {z} is innocuous")
  IO.println s!"{label}: fl {p} (fl {p'} {z}) = {a}, fl {p} {z} = {b}"

-- Figueroa's examples for `p = 4`, as in Roux's Remarks 11, 21 and 30.
#eval checkDiffers "sum, p = 4" 4 8 (9 / 8 + 15 / 256)
#eval checkDiffers "product, p = 4" 4 7 (13 / 8 * (13 / 8))
#eval checkDiffers "quotient, p = 4" 4 7 (1 / (15 / 16))

-- The families of the proofs.
#eval show IO Unit from do
  for p in [2, 3, 5, 8] do
    let a : ℚ := 2 ^ (p - 1)
    checkDiffers s!"sum, p = {p}" p (2 * p) (1 + 1 / a + (1 / (2 * a) - 1 / (4 * a * a)))
    checkDiffers s!"quotient, p = {p}" p (2 * p - 1) (1 / (1 - 1 / (2 * a)))
  for p in [5, 6, 9] do
    let x : ℚ := 3 * 2 ^ (p - 2) - 1
    checkDiffers s!"product, p = {p}" p (2 * p - 1) (x * x)

/-! Exhaustive checks of innocuous double rounding -/

/-- Zero and the floats `m 2^e` with `0 < |m| < 2^p` and `e` in `[e₀, e₀ + n)`. -/
private meta def floats (p : ℕ) (e₀ : ℤ) (n : ℕ) : List ℚ := Id.run do
  let mut xs : List ℚ := [0]
  for m in [1:2 ^ p] do
    for i in [0:n] do
      let v : ℚ := (m : ℚ) * (2 : ℚ) ^ (e₀ + i)
      xs := v :: (-v) :: xs
  return xs

#eval show IO Unit from do
  let xs := floats 3 (-3) 7
  let mut pairs := 0
  for x in xs do
    for y in xs do
      pairs := pairs + 1
      unless fl 3 (fl 7 (x + y)) == fl 3 (x + y) do
        throw (IO.userError s!"sum {x} + {y}")
      unless fl 3 (fl 7 (x - y)) == fl 3 (x - y) do
        throw (IO.userError s!"difference {x} - {y}")
      unless fl 3 (fl 6 (x * y)) == fl 3 (x * y) do
        throw (IO.userError s!"product {x} * {y}")
      unless fl 3 (fl 6 (x / y)) == fl 3 (x / y) do
        throw (IO.userError s!"quotient {x} / {y}")
  IO.println s!"p = 3: double rounding is innocuous on all {pairs} pairs"

/-! Gradual underflow -/

#eval show IO Unit from do
  let xs := floats 2 0 5
  let mut pairs := 0
  for x in xs do
    for y in xs do
      pairs := pairs + 1
      unless flIn 2 0 (flIn 5 (-4) (x + y)) == flIn 2 0 (x + y) do
        throw (IO.userError s!"sum {x} + {y}")
      unless flIn 2 0 (flIn 5 (-4) (x - y)) == flIn 2 0 (x - y) do
        throw (IO.userError s!"difference {x} - {y}")
      unless flIn 2 0 (flIn 4 (-4) (x * y)) == flIn 2 0 (x * y) do
        throw (IO.userError s!"product {x} * {y}")
      unless flIn 2 0 (flIn 4 (-4) (x / y)) == flIn 2 0 (x / y) do
        throw (IO.userError s!"quotient {x} / {y}")
  IO.println s!"p = 2, q = 0, q' = -4: double rounding is innocuous on all {pairs} pairs"

#eval check "flIn, subnormal" (flIn 2 0 (3 / 4 : ℚ)) 1
#eval check "flIn, normal" (flIn 2 0 (5 : ℚ)) 4
#eval check "q' = q: direct" (flIn 2 0 (16 / 3 : ℚ)) 6
#eval check "q' = q: through 4 bits" (flIn 2 0 (flIn 4 0 (16 / 3 : ℚ))) 4

/-! Closed checks -/

/-- Binary32 operations evaluated in binary64 without underflow. -/
example (x y : ℝ) (hx : IsFloat 24 x) (hy : IsFloat 24 y) :
    fl 24 (fl 53 (x + y)) = fl 24 (x + y) ∧ fl 24 (fl 53 (x * y)) = fl 24 (x * y) ∧
      fl 24 (fl 53 (x / y)) = fl 24 (x / y) ∧ fl 24 (fl 53 √x) = fl 24 √x :=
  ⟨fl_fl_add (by norm_num) (by norm_num) hx hy, fl_fl_mul (by norm_num) (by norm_num) hx hy,
    fl_fl_div (by norm_num) (by norm_num) hx hy, fl_fl_sqrt (by norm_num) (by norm_num) hx⟩

/-- Binary64 operations evaluated in a 128-bit format (113-bit significands, least exponent
`-16494`) with gradual underflow. -/
example (x y : ℝ) (hx : IsFloatIn 53 (-1074) 971 x) (hy : IsFloatIn 53 (-1074) 971 y) :
    flIn 53 (-1074) (flIn 113 (-16494) (x / y)) = flIn 53 (-1074) (x / y) :=
  flIn_flIn_div (by norm_num) (by norm_num) (by norm_num) hx hy

/-- The x87 counterexample with 64-bit intermediate precision for binary64. -/
example : fl 53 (fl 64 (1 + ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ)))) ≠
    fl 53 (1 + ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ))) := by
  obtain ⟨-, -, h₁, -, h₂⟩ := innocuous_double_rounding.1
  rw [h₁, h₂]
  norm_num

/-- The optimality counterexample for square roots with `p = 24`. -/
example : ∃ x : ℝ, IsFloat 24 x ∧ 0 ≤ x ∧ fl 24 (fl 49 √x) ≠ fl 24 √x :=
  innocuous_double_rounding.2.2.2.2.2.1 24 (by norm_num)

#print axioms innocuous_double_rounding
#print axioms fl_fl_eq_of_near
#print axioms fl_fl_add
#print axioms fl_fl_mul
#print axioms fl_fl_div
#print axioms fl_fl_sqrt
#print axioms flIn_flIn_add
#print axioms flIn_flIn_mul
#print axioms flIn_flIn_div
#print axioms flIn_flIn_sqrt
#print axioms binary32_via_binary64

end Cslib.Algorithms.Lean.FloatingPoint
