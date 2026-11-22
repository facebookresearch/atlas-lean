/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Floor
public meta import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint
public meta import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Data.Rat.Floor

/-!
# Tests for the floating-point rounding model

Executed fixtures over `ℚ`, with `p = 3` significand bits unless stated:
* `fl (1/3) = 5/16` with error `1/48 ≤ (1/8)(1/3)`; `fl` fixes floats; a negative value.
* Ties to even: `9/8 ↦ 1` (significand `4`, not `5`), `11/8 ↦ 3/2` (`6`, not `5`),
  `15/8 ↦ 2` (`8`, a carry into the next binade, not `7`), and `-11/8 ↦ -3/2`.
* Sterbenz: `7/4 - 1 = 3/4` is exact; `7/4 - 1/8 = 13/8` violates the condition and needs four
  bits, so it rounds (to `3/2`).
* 2000 random rationals for `p = 3, 5, 8, 24`: the relative error bound holds, `fl x` is a float
  (its significand at `ulpExp` or `ulpExp + 1` has at most `p` bits), and no float with
  significand `|m| < 2^p` at exponents `ulpExp - 2 … ulpExp + 2` is closer.
* Exhaustively for `p = 4`, all pairs of floats `x, y > 0` with significands below `16` and
  exponents in `[-3, 3]`: whenever `y / 2 ≤ x ≤ 2 y`, `fl (x - y) = x - y`.

Closed checks evaluate `fl` with `decide +kernel` and instantiate the theorems over `ℝ`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint

private meta def check (label : String) (p : ℕ) (x expected : ℚ) : IO Unit := do
  let r := fl p x
  unless r == expected do throw (IO.userError s!"{label}: fl {p} {x} = {r}, expected {expected}")
  IO.println s!"{label}: fl {p} ({x}) = {r}"

#eval check "one third" 3 (1 / 3) (5 / 16)
#eval check "a float is fixed" 3 (5 / 16) (5 / 16)
#eval check "negative" 3 (-1 / 3) (-5 / 16)
#eval check "tie, even below" 3 (9 / 8) 1
#eval check "tie, even above" 3 (11 / 8) (3 / 2)
#eval check "tie, carry into the next binade" 3 (15 / 8) 2
#eval check "negative tie" 3 (-11 / 8) (-3 / 2)
#eval check "Sterbenz: exact" 3 (7 / 4 - 1) (3 / 4)
#eval check "outside Sterbenz: rounded" 3 (7 / 4 - 1 / 8) (3 / 2)
#eval check "zero" 3 0 0

/-- A deterministic linear congruential generator. -/
private meta def nextSeed (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- The significand of `y` at the exponent `e`, if it is an integer with at most `p` bits. -/
private meta def sigAt (p : ℕ) (y : ℚ) (e : ℤ) : Bool :=
  let s := y / (2 : ℚ) ^ e
  s.den == 1 && s.num.natAbs < 2 ^ p

private meta def randomCheck (p : ℕ) (count : ℕ) (seed : ℕ) : IO Unit := do
  let mut s := seed
  for i in [0:count] do
    s := nextSeed s
    let num : ℤ := (s / 3 % 2000001 : ℕ) - 1000000
    s := nextSeed s
    let den : ℕ := 1 + s / 3 % 9999
    let x : ℚ := num / den
    let r := fl p x
    let e := ulpExp p x
    unless |r - x| ≤ (2 : ℚ) ^ (-(p : ℤ)) * |x| do
      throw (IO.userError s!"p = {p}, x = {x}: relative error bound fails")
    unless sigAt p r e || sigAt p r (e + 1) do
      throw (IO.userError s!"p = {p}, x = {x}: fl x = {r} is not a float")
    for d in [0:5] do
      let ee := e + d - 2
      let c := x / (2 : ℚ) ^ ee
      for m in [c.floor - 1, c.floor, c.floor + 1, c.floor + 2] do
        if m.natAbs < 2 ^ p then
          let f := (m : ℚ) * (2 : ℚ) ^ ee
          unless |r - x| ≤ |f - x| do
            throw (IO.userError s!"p = {p}, x = {x}: {f} is closer than fl x = {r} ({i})")
  IO.println s!"p = {p}: {count} random rationals, error bound, float and nearest checks pass"

#eval randomCheck 3 500 11
#eval randomCheck 5 500 23
#eval randomCheck 8 500 37
#eval randomCheck 24 500 41

#eval show IO Unit from do
  let mut floats : List ℚ := []
  for m in [1:16] do
    for e in [0:7] do
      floats := ((m : ℚ) * (2 : ℚ) ^ ((e : ℤ) - 3)) :: floats
  let mut pairs := 0
  for x in floats do
    for y in floats do
      if y / 2 ≤ x && x ≤ 2 * y then
        pairs := pairs + 1
        unless fl 4 (x - y) == x - y do
          throw (IO.userError s!"Sterbenz fails for {x} - {y}")
  IO.println s!"p = 4: Sterbenz holds on all {pairs} pairs within a factor of two"

/-! Closed checks -/

example : fl 3 (9 / 8 : ℚ) = 1 := by decide +kernel
example : fl 3 (15 / 8 : ℚ) = 2 := by decide +kernel

/-- Over the reals: double precision has unit roundoff `2^(-53)`. -/
example (x : ℝ) : |fl 53 x - x| ≤ 2 ^ (-(53 : ℤ)) * |x| := abs_fl_sub_le x

example (x y : ℝ) (hx : IsFloat 53 x) (hy : IsFloat 53 y) (h₁ : y / 2 ≤ x) (h₂ : x ≤ 2 * y) :
    fl 53 (x - y) = x - y :=
  fl_sub_eq_sub (by norm_num) hx hy h₁ h₂

/-- IEEE 754 binary64: `emin = -1022`, `emax = 1023`, so `qmin = -1074` and `qmax = 971`. -/
example (x : ℝ) (hlo : (2 : ℝ) ^ ((-1074 : ℤ) + ((53 : ℤ) - 1)) ≤ |x|)
    (hhi : |x| ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ)) : IsFloatIn 53 (-1074) 971 (fl 53 x) :=
  isFloatIn_fl (by norm_num) hlo hhi

#print axioms abs_fl_sub_le
#print axioms abs_fl_sub_le_of_isFloat
#print axioms isFloat_fl
#print axioms isFloatIn_fl
#print axioms isFloat_sub
#print axioms isFloatIn_sub

end Cslib.Algorithms.Lean.FloatingPoint
