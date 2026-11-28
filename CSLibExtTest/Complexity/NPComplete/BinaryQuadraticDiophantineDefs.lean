/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BinaryQuadraticDiophantineDefs

namespace MetaMathlibExt.Complexity.NPComplete.BinaryQuadraticDiophantine

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : BinaryQuadraticDiophantineInstance) :
    binaryQuadraticDiophantineDec (bitEncode i) = true ↔ BinaryQuadraticDiophantineFeasible i := by
  simp [binaryQuadraticDiophantineDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : binaryQuadraticDiophantineDec [true] = false := by
  have h : bitDecode (α := BinaryQuadraticDiophantineInstance) [true] = none := rfl
  simp [binaryQuadraticDiophantineDec, h]

/-- `x₁² + x₂² - 25 = 0` has the nonnegative solution `(3, 4)`. -/
example : binaryQuadraticDiophantineDec (bitEncode
    (((1, 0), (0, 0), (1, 0), (0, 0), (0, 0), (0, 25)) : BinaryQuadraticDiophantineInstance)) =
    true :=
  (accepts_encoding _).2 ⟨3, 4, by decide⟩

/-- `3` is not a sum of two squares, so `x₁² + x₂² - 3 = 0` has no nonnegative solution. -/
example : binaryQuadraticDiophantineDec (bitEncode
    (((1, 0), (0, 0), (1, 0), (0, 0), (0, 0), (0, 3)) : BinaryQuadraticDiophantineInstance)) =
    false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨a, b, h⟩
  have h' : a ^ 2 + b ^ 2 = 3 := by
    simp [eval, intOf] at h
    have : ((a ^ 2 + b ^ 2 : ℕ) : ℤ) = 3 := by push_cast; omega
    exact_mod_cast this
  have ha : a < 2 := by
    by_contra hc
    have := Nat.pow_le_pow_left (Nat.le_of_not_lt hc) 2
    omega
  have hb : b < 2 := by
    by_contra hc
    have := Nat.pow_le_pow_left (Nat.le_of_not_lt hc) 2
    omega
  have key : ∀ a < 2, ∀ b < 2, a ^ 2 + b ^ 2 ≠ 3 := by decide
  exact key a ha b hb h'

end MetaMathlibExt.Complexity.NPComplete.BinaryQuadraticDiophantine
