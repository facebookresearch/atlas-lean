/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DivideAndConquer.Karatsuba
public meta import CSLibExt.Algorithms.Lean.DivideAndConquer.Karatsuba

/-!
# Karatsuba multiplication tests

Executed fixtures compare the returned product with `*` and the cost with the closed form, in
bases 2 and 10, at power-of-two and other digit counts, with zero and maximal operands, and with
operands whose halves make both signs of the middle difference occur. Closed examples check
the cost recurrence and the operand-size lemma.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private meta def check (label : String) (B n x y cost : Nat) : IO Unit := do
  let result := karatsuba B n x y
  unless result.ret == x * y && result.time == cost do
    throw (IO.userError s!"{label}: got {result.ret} with cost {result.time}")
  IO.println s!"{label}: {result.ret}, cost {result.time}"

#eval check "one digit" 10 1 7 8 1
#eval check "zero digits" 10 0 0 0 1
#eval check "2 digits base 10" 10 2 12 34 5
#eval check "4 digits base 10, a ≥ b and c < d" 10 4 4321 1234 19
#eval check "4 digits base 10, a ≥ b and c ≥ d" 10 4 4321 8765 19
#eval check "4 digits base 10, maximal" 10 4 9999 9999 19
#eval check "4 digits base 10, a < b and c < d" 10 4 1299 3488 19
#eval check "4 digits base 10, a < b and c ≥ d" 10 4 1299 8834 19
#eval check "8 digits base 10" 10 8 12345678 87654321 65
#eval check "8 digits base 2" 2 8 0b10110101 0b11001110 65
#eval check "3 digits base 10" 10 3 999 999 18
#eval check "5 digits base 10, zero operand" 10 5 0 54321 59
#eval check "16 digits base 10" 10 16 3141592653589793 2718281828459045 211
#eval check "operands wider than n still multiply" 10 2 123456 789 5

example : karatsubaCost 1 = 1 := karatsubaCost_of_le_one le_rfl
example : karatsubaCost 3 = 18 := by
  simp [karatsubaCost_of_two_le, karatsubaCost_of_le_one]
example : karatsubaCost 5 = 59 := by
  simp [karatsubaCost_of_two_le, karatsubaCost_of_le_one]
example : karatsubaCost 16 = 211 := by
  simp [karatsubaCost_of_two_le, karatsubaCost_of_le_one]

example : (karatsuba 10 4 1234 5678).ret = 7006652 := by
  rw [karatsuba_ret]
example (k : ℕ) : karatsubaCost (2 ^ k) + 2 ^ (k + 1) = 3 ^ (k + 1) := karatsubaCost_two_pow k

example (B n x y : ℕ) : (karatsuba B n x y).ret = x * y := karatsuba_ret B n x y

example (B n x y : ℕ) : (karatsuba B n x y).time ≤ 3 ^ (Nat.clog 2 n + 1) :=
  karatsuba_time_le B n x y

example (B n x y : ℕ) (hn : 1 ≤ n) :
    ((karatsuba B n x y).time : ℝ) ≤ 9 * (n : ℝ) ^ Real.logb 2 3 :=
  karatsuba_time_le_rpow B hn x y

/-- `9999 < 10^4`, so its halves `99` and `99` and their difference `0` are two-digit. -/
example : 9999 / 10 ^ 2 < 10 ^ 2 ∧ 9999 % 10 ^ 2 < 10 ^ 2 ∧
    Nat.dist (9999 / 10 ^ 2) (9999 % 10 ^ 2) < 10 ^ 2 :=
  karatsuba_operands_lt (n := 4) (by norm_num) (by norm_num)

#print axioms karatsuba
#print axioms karatsuba_ret
#print axioms karatsuba_time
#print axioms karatsuba_operands_lt
#print axioms karatsubaCost_two_pow
#print axioms karatsubaCost_le
#print axioms karatsuba_time_le
#print axioms karatsuba_time_le_rpow

end Cslib.Algorithms.Lean.TimeM
