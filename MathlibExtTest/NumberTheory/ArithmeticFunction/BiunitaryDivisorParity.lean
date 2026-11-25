/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Prime.Basic
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisorParity

open MetaMathlibExt

-- The power-of-two case includes exponent zero and a square with its middle divisor omitted.
example : Odd (sigmaBiunitary 1) :=
  (odd_sigmaBiunitary_iff 1 (by decide)).2 ⟨0, rfl⟩

example : Odd (sigmaBiunitary 4) :=
  (odd_sigmaBiunitary_iff 4 (by decide)).2 ⟨2, rfl⟩

-- In an odd square the middle divisor is again omitted, leaving an even sum.
example : sigmaBiunitary 9 = 10 := by decide

-- An odd factor of a power of two would have to divide 2 itself.
private theorem not_odd_sigmaBiunitary_of_three_dvd (n : ℕ) (hn : 0 < n) (h3 : 3 ∣ n) :
    ¬ Odd (sigmaBiunitary n) := by
  rw [odd_sigmaBiunitary_iff n hn]
  rintro ⟨k, rfl⟩
  exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide) h3)

example : ¬ Odd (sigmaBiunitary 9) := not_odd_sigmaBiunitary_of_three_dvd 9 (by decide) (by decide)

-- Multiplying a power of two by 3 changes the parity, for every exponent.
example (k : ℕ) : Odd (sigmaBiunitary (2 ^ k)) ∧ ¬ Odd (sigmaBiunitary (3 * 2 ^ k)) := by
  have hk : 0 < (2 : ℕ) ^ k := Nat.pow_pos (by decide)
  exact ⟨(odd_sigmaBiunitary_iff _ hk).2 ⟨k, rfl⟩,
    not_odd_sigmaBiunitary_of_three_dvd _ (Nat.mul_pos (by decide) hk) ⟨2 ^ k, rfl⟩⟩

example : sigmaBiunitary 12 = 20 := by decide

example : ¬ Odd (sigmaBiunitary 12) :=
  not_odd_sigmaBiunitary_of_three_dvd 12 (by decide) (by decide)
