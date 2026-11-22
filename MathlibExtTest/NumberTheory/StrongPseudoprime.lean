/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.StrongPseudoprime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace MetaMathlibExtTest

open MetaMathlibExt

example : IsStrongPseudoprime 2047 2 := isStrongPseudoprime_2047_two

example : IsStrongPseudoprime 9 1 := isStrongPseudoprime_one (by norm_num) (by norm_num) (by decide)

/-- `9` is not a strong pseudoprime to base `2`: `8 = 2 ^ 3 * 1`, `2 ^ 1 = 2 ≠ 1`, and
`2, 4, 16 = 7` are never `-1 = 8` in `ZMod 9`. -/
example : ¬IsStrongPseudoprime 9 2 := by
  rintro ⟨-, -, -, k, d, hkd, hd, h⟩
  have hk : k = 3 ∧ d = 1 := by
    have h8 : 2 ^ k * d = 8 := by omega
    obtain ⟨m, rfl⟩ := hd
    have hk3 : k ≤ 3 := by
      by_contra hk
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ k ≤ 2 ^ k * (2 * m + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    interval_cases k <;> omega
  obtain ⟨rfl, rfl⟩ := hk
  rcases h with h | ⟨i, hi, h⟩
  · revert h; decide
  · interval_cases i <;> revert h <;> decide

/-- A prime is never a strong pseudoprime. -/
example {p : ℕ} (hp : p.Prime) (b : ZMod p) : ¬IsStrongPseudoprime p b :=
  fun h => h.not_prime hp

end MetaMathlibExtTest
