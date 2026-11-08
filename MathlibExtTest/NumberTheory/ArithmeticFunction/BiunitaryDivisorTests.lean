/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor

@[expose] public section

open MetaMathlibExt

example : gcdUnitary 2 2 = 2 := by decide

example : gcdUnitary 4 2 = 1 := by decide

example : biunitaryDivisors 4 = {1, 4} := by decide

example : biunitaryDivisors 12 = {1, 3, 4, 12} := by decide

example : sigmaBiunitary 8 = 15 := by decide

example : sigmaBiunitary 672 = 3 * 672 := by decide

example {n d : ℕ} :
    d ∈ biunitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ gcdUnitary d (n / d) = 1 := by
  rw [mem_biunitaryDivisors]

example : biunitaryDivisors 0 = ∅ := by simp

example : sigmaBiunitary 0 = 0 := by simp

example {n d : ℕ} (h : d ∈ biunitaryDivisors n) : d ∣ n :=
  dvd_of_mem_biunitaryDivisors h

example (a b : ℕ) : gcdUnitary a b = gcdUnitary b a := gcdUnitary_comm a b

example (b : ℕ) : gcdUnitary 0 b = 0 := by simp

example {a b d : ℕ} (ha : d ∈ a.unitaryDivisors) (hb : d ∈ b.unitaryDivisors) :
    d ≤ gcdUnitary a b :=
  le_gcdUnitary ha hb

example : gcdUnitary 12 18 ∈ Nat.unitaryDivisors 12 ∧ gcdUnitary 12 18 ∈ Nat.unitaryDivisors 18 :=
  gcdUnitary_mem_unitaryDivisors (by decide) (by decide)

example : gcdUnitary 12 18 = 1 := by decide

example {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : 0 < gcdUnitary a b := gcdUnitary_pos ha hb
