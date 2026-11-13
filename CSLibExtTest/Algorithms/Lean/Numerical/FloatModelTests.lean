/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Rat.Floor
meta import MathlibExt.Data.Float.Model
meta import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint
meta import Mathlib.Data.Rat.Floor

/-!
# Actual core model versus Atlas rounding

The 26 fixed pairs exercise decoded witnesses, the inclusive exact-result
interval, and both actual implementations. Twenty pairs are in scope; six
deliberately cover zero, underflow, subnormal results and overflow. Three
nonfinite encodings have no rational value. These are ordinary `#eval`
assertions, not kernel proofs of the operation bridge.
-/

open Cslib.Algorithms.Lean.FloatingPoint

private meta structure Case where
  label : String
  multiply : Bool
  aBits : UInt64
  bBits : UInt64
  x : Rat
  y : Rat
  exact : Rat
  rounded : Rat
  result : Option Rat
  inScope : Bool
  aSubnormal : Bool
  bSubnormal : Bool

private meta def subnormal (f : Float.Model) : Bool :=
  match f.unpack with
  | .finite _ m _ _ => m < 2 ^ 52
  | _ => false

private meta def checkEqual {α : Type} [BEq α] [ToString α]
    (label field : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw (IO.userError s!"{label}: {field}={actual}, expected {expected}")

private meta def checkCase (c : Case) : IO Bool := do
  let a := Float.Model.ofBits c.aBits
  let b := Float.Model.ofBits c.bBits
  checkEqual c.label "a bits" a.toBits c.aBits
  checkEqual c.label "b bits" b.toBits c.bBits
  let some x := a.toRat? | throw (IO.userError s!"{c.label}: a is nonfinite")
  let some y := b.toRat? | throw (IO.userError s!"{c.label}: b is nonfinite")
  checkEqual c.label "a witness" x c.x
  checkEqual c.label "b witness" y c.y
  checkEqual c.label "a subnormal" (subnormal a) c.aSubnormal
  checkEqual c.label "b subnormal" (subnormal b) c.bSubnormal
  let exact := if c.multiply then x * y else x + y
  let inScope := decide ((2 : Rat) ^ (-1022 : Int) ≤ |exact| ∧
    |exact| ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int))
  checkEqual c.label "exact" exact c.exact
  checkEqual c.label "scope" inScope c.inScope
  let result := if c.multiply then Float.Model.mul a b else Float.Model.add a b
  let rounded := fl 53 exact
  checkEqual c.label "Atlas fl53" rounded c.rounded
  checkEqual c.label "model result" result.toRat? c.result
  if inScope then
    checkEqual c.label "in-contract agreement" result.toRat? (some rounded)
  IO.println (s!"CASE|{c.label}|{c.multiply}|{a.toBits}|{b.toBits}|{x}|{y}|" ++
    s!"{exact}|{inScope}|{result.toRat?}|{rounded}|{result.toBits}|" ++
    s!"{subnormal a}|{subnormal b}")
  return inScope

-- BEGIN FROZEN FIXTURES
private meta def cases : List Case := [
  ⟨"add_plus_zero_min_normal", false,
    0x0000000000000000, 0x0010000000000000,
    0, ((2 : Rat) ^ (-1022 : Int)),
    ((2 : Rat) ^ (-1022 : Int)), ((2 : Rat) ^ (-1022 : Int)),
    some ((2 : Rat) ^ (-1022 : Int)), true, false, false⟩,
  ⟨"add_minus_zero_min_normal", false,
    0x8000000000000000, 0x0010000000000000,
    0, ((2 : Rat) ^ (-1022 : Int)),
    ((2 : Rat) ^ (-1022 : Int)), ((2 : Rat) ^ (-1022 : Int)),
    some ((2 : Rat) ^ (-1022 : Int)), true, false, false⟩,
  ⟨"add_minus_zero_negative_min_normal", false,
    0x8000000000000000, 0x8010000000000000,
    0, (-1 * (2 : Rat) ^ (-1022 : Int)),
    (-1 * (2 : Rat) ^ (-1022 : Int)), (-1 * (2 : Rat) ^ (-1022 : Int)),
    some (-1 * (2 : Rat) ^ (-1022 : Int)), true, false, false⟩,
  ⟨"add_two_subnormal_inputs", false,
    0x000fffffffffffff, 0x0000000000000001,
    (4503599627370495 * (2 : Rat) ^ (-1074 : Int)), ((2 : Rat) ^ (-1074 : Int)),
    ((2 : Rat) ^ (-1022 : Int)), ((2 : Rat) ^ (-1022 : Int)),
    some ((2 : Rat) ^ (-1022 : Int)), true, true, true⟩,
  ⟨"add_negative_subnormal_inputs", false,
    0x800fffffffffffff, 0x8000000000000001,
    (-4503599627370495 * (2 : Rat) ^ (-1074 : Int)), (-1 * (2 : Rat) ^ (-1074 : Int)),
    (-1 * (2 : Rat) ^ (-1022 : Int)), (-1 * (2 : Rat) ^ (-1022 : Int)),
    some (-1 * (2 : Rat) ^ (-1022 : Int)), true, true, true⟩,
  ⟨"add_normal_subnormal_cancellation", false,
    0x0010000000000001, 0x8000000000000001,
    (4503599627370497 * (2 : Rat) ^ (-1074 : Int)), (-1 * (2 : Rat) ^ (-1074 : Int)),
    ((2 : Rat) ^ (-1022 : Int)), ((2 : Rat) ^ (-1022 : Int)),
    some ((2 : Rat) ^ (-1022 : Int)), true, false, true⟩,
  ⟨"add_severe_normal_cancellation", false,
    0x4330000000000000, 0xc32fffffffffffff,
    ((2 : Rat) ^ (52 : Int)), (-9007199254740991 * (2 : Rat) ^ (-1 : Int)),
    ((2 : Rat) ^ (-1 : Int)), ((2 : Rat) ^ (-1 : Int)),
    some ((2 : Rat) ^ (-1 : Int)), true, false, false⟩,
  ⟨"add_max_finite_zero", false,
    0x7fefffffffffffff, 0x0000000000000000,
    (9007199254740991 * (2 : Rat) ^ (971 : Int)), 0,
    (9007199254740991 * (2 : Rat) ^ (971 : Int)), (9007199254740991 * (2 : Rat) ^ (971 : Int)),
    some (9007199254740991 * (2 : Rat) ^ (971 : Int)), true, false, false⟩,
  ⟨"add_reaches_max_finite", false,
    0x7feffffffffffffe, 0x7ca0000000000000,
    (4503599627370495 * (2 : Rat) ^ (972 : Int)), ((2 : Rat) ^ (971 : Int)),
    (9007199254740991 * (2 : Rat) ^ (971 : Int)), (9007199254740991 * (2 : Rat) ^ (971 : Int)),
    some (9007199254740991 * (2 : Rat) ^ (971 : Int)), true, false, false⟩,
  ⟨"add_tie_even_below", false,
    0x3ff0000000000000, 0x3ca0000000000000,
    1, ((2 : Rat) ^ (-53 : Int)),
    (9007199254740993 * (2 : Rat) ^ (-53 : Int)), 1,
    some 1, true, false, false⟩,
  ⟨"add_tie_even_above", false,
    0x3ff0000000000001, 0x3ca0000000000000,
    (4503599627370497 * (2 : Rat) ^ (-52 : Int)), ((2 : Rat) ^ (-53 : Int)),
    (9007199254740995 * (2 : Rat) ^ (-53 : Int)), (2251799813685249 * (2 : Rat) ^ (-51 : Int)),
    some (2251799813685249 * (2 : Rat) ^ (-51 : Int)), true, false, false⟩,
  ⟨"add_tie_carry", false,
    0x3fffffffffffffff, 0x3ca0000000000000,
    (9007199254740991 * (2 : Rat) ^ (-52 : Int)), ((2 : Rat) ^ (-53 : Int)),
    (18014398509481983 * (2 : Rat) ^ (-53 : Int)), ((2 : Rat) ^ (1 : Int)),
    some ((2 : Rat) ^ (1 : Int)), true, false, false⟩,
  ⟨"add_negative_tie", false,
    0xbff0000000000001, 0xbca0000000000000,
    (-4503599627370497 * (2 : Rat) ^ (-52 : Int)), (-1 * (2 : Rat) ^ (-53 : Int)),
    (-9007199254740995 * (2 : Rat) ^ (-53 : Int)), (-2251799813685249 * (2 : Rat) ^ (-51 : Int)),
    some (-2251799813685249 * (2 : Rat) ^ (-51 : Int)), true, false, false⟩,
  ⟨"mul_subnormal_input_normal_result", true,
    0x0000000000000001, 0x4330000000000000,
    ((2 : Rat) ^ (-1074 : Int)), ((2 : Rat) ^ (52 : Int)),
    ((2 : Rat) ^ (-1022 : Int)), ((2 : Rat) ^ (-1022 : Int)),
    some ((2 : Rat) ^ (-1022 : Int)), true, true, false⟩,
  ⟨"mul_negative_subnormal_input", true,
    0x8000000000000001, 0x4330000000000000,
    (-1 * (2 : Rat) ^ (-1074 : Int)), ((2 : Rat) ^ (52 : Int)),
    (-1 * (2 : Rat) ^ (-1022 : Int)), (-1 * (2 : Rat) ^ (-1022 : Int)),
    some (-1 * (2 : Rat) ^ (-1022 : Int)), true, true, false⟩,
  ⟨"mul_min_normal_one", true,
    0x0010000000000000, 0x3ff0000000000000,
    ((2 : Rat) ^ (-1022 : Int)), 1,
    ((2 : Rat) ^ (-1022 : Int)), ((2 : Rat) ^ (-1022 : Int)),
    some ((2 : Rat) ^ (-1022 : Int)), true, false, false⟩,
  ⟨"mul_max_finite_one", true,
    0x7fefffffffffffff, 0x3ff0000000000000,
    (9007199254740991 * (2 : Rat) ^ (971 : Int)), 1,
    (9007199254740991 * (2 : Rat) ^ (971 : Int)), (9007199254740991 * (2 : Rat) ^ (971 : Int)),
    some (9007199254740991 * (2 : Rat) ^ (971 : Int)), true, false, false⟩,
  ⟨"mul_tie", true,
    0x3ff8000000000000, 0x3ff0000000000001,
    (3 * (2 : Rat) ^ (-1 : Int)), (4503599627370497 * (2 : Rat) ^ (-52 : Int)),
    (13510798882111491 * (2 : Rat) ^ (-53 : Int)), (3377699720527873 * (2 : Rat) ^ (-51 : Int)),
    some (3377699720527873 * (2 : Rat) ^ (-51 : Int)), true, false, false⟩,
  ⟨"mul_tie_carry", true,
    0x3ff8000000000000, 0x3ff5555555555555,
    (3 * (2 : Rat) ^ (-1 : Int)), (6004799503160661 * (2 : Rat) ^ (-52 : Int)),
    (18014398509481983 * (2 : Rat) ^ (-53 : Int)), ((2 : Rat) ^ (1 : Int)),
    some ((2 : Rat) ^ (1 : Int)), true, false, false⟩,
  ⟨"mul_negative_times_negative_max", true,
    0xffefffffffffffff, 0xbff0000000000000,
    (-9007199254740991 * (2 : Rat) ^ (971 : Int)), (-1),
    (9007199254740991 * (2 : Rat) ^ (971 : Int)), (9007199254740991 * (2 : Rat) ^ (971 : Int)),
    some (9007199254740991 * (2 : Rat) ^ (971 : Int)), true, false, false⟩,
  ⟨"excluded_exact_subnormal_result", true,
    0x0010000000000000, 0x3fe0000000000000,
    ((2 : Rat) ^ (-1022 : Int)), ((2 : Rat) ^ (-1 : Int)),
    ((2 : Rat) ^ (-1023 : Int)), ((2 : Rat) ^ (-1023 : Int)),
    some ((2 : Rat) ^ (-1023 : Int)), false, false, false⟩,
  ⟨"excluded_underflow_half_min_subnormal", true,
    0x0000000000000001, 0x3fe0000000000000,
    ((2 : Rat) ^ (-1074 : Int)), ((2 : Rat) ^ (-1 : Int)),
    ((2 : Rat) ^ (-1075 : Int)), ((2 : Rat) ^ (-1075 : Int)),
    some 0, false, true, false⟩,
  ⟨"excluded_overflow_tie", false,
    0x7fefffffffffffff, 0x7c90000000000000,
    (9007199254740991 * (2 : Rat) ^ (971 : Int)), ((2 : Rat) ^ (970 : Int)),
    (18014398509481983 * (2 : Rat) ^ (970 : Int)), ((2 : Rat) ^ (1024 : Int)),
    none, false, false, false⟩,
  ⟨"excluded_overflow_product", true,
    0x7fefffffffffffff, 0x4000000000000000,
    (9007199254740991 * (2 : Rat) ^ (971 : Int)), ((2 : Rat) ^ (1 : Int)),
    (9007199254740991 * (2 : Rat) ^ (972 : Int)), (9007199254740991 * (2 : Rat) ^ (972 : Int)),
    none, false, false, false⟩,
  ⟨"excluded_zero_product", true,
    0x8000000000000000, 0x3ff0000000000000,
    0, 1,
    0, 0,
    some 0, false, false, false⟩,
  ⟨"excluded_exact_cancellation", false,
    0x3ff0000000000000, 0xbff0000000000000,
    1, (-1),
    0, 0,
    some 0, false, false, false⟩
]
-- END FROZEN FIXTURES

#eval show IO Unit from do
  checkEqual "suite" "pairs" cases.length 26
  let mut inScope := 0
  for c in cases do
    if ← checkCase c then inScope := inScope + 1
  checkEqual "suite" "in scope" inScope 20
  checkEqual "suite" "excluded" (cases.length - inScope) 6
  let nonfinite : List UInt64 :=
    [0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000]
  for bits in nonfinite do
    let f := Float.Model.ofBits bits
    checkEqual "nonfinite" "preserved bits" f.toBits bits
    checkEqual "nonfinite" "value" f.toRat? none
    checkEqual "nonfinite" "isFinite" f.isFinite false
    IO.println s!"NONFINITE|{bits}|{f.toRat?}|{f.isFinite}"
  IO.println (s!"COUNTS|{cases.length}|{inScope}|{cases.length - inScope}|" ++
    s!"{nonfinite.length}")
