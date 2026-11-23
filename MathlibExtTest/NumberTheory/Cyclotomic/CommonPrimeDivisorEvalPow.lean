/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Cyclotomic.CommonPrimeDivisorEvalPow
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for `MathlibExt.NumberTheory.Cyclotomic.CommonPrimeDivisorEvalPow` -/

namespace MathlibExtTest.CommonPrimeDivisorEvalPow

open MetaMathlibExt Polynomial

-- At `x = 1`, every prime divides `x - 1`, so the cyclotomic value alone determines `ρ`.
example {ρ p : ℕ} (hρ : ρ.Prime) (hp : p.Prime) (h : (ρ : ℤ) ∣ (cyclotomic p ℤ).eval 1) :
    ρ = p :=
  prime_eq_of_dvd_sub_one_of_dvd_cyclotomic_eval (x := 1) hρ hp (by decide) (by simp) h

-- The hypotheses can hold together, here with `ρ = p = 3`, `a = 2` and `y = 4`:
-- `3 ∣ 4 - 1` and `3 ∣ Φ_3(4 ^ 3) = 64 ^ 2 + 64 + 1 = 3 * 1387`.
example : (3 : ℤ) ∣ 4 - 1 ∧ (3 : ℤ) ∣ (cyclotomic 3 ℤ).eval (4 ^ 3 ^ (2 - 1)) := by
  norm_num [cyclotomic_three]

-- Since `5 ∣ 6 - 1` and `5 ≠ 3`, the prime `5` divides no `Φ_3(6 ^ 3 ^ (a - 1))` with `a ≥ 1`.
example {a : ℕ} (ha : 0 < a) : ¬ (5 : ℤ) ∣ (cyclotomic 3 ℤ).eval (6 ^ 3 ^ (a - 1)) := fun h ↦
  absurd (prime_eq_of_dvd_sub_one_of_dvd_cyclotomic_eval_pow (by norm_num) (by norm_num) ha
    (by norm_num) (by norm_num) h) (by norm_num)

-- For `p = 2` we have `Φ_2(x) = x + 1`: since `3 ∣ 4 - 1`, no `4 ^ 2 ^ (a - 1) + 1` with `a ≥ 1`
-- is a multiple of `3`.
example {a : ℕ} (ha : 0 < a) : ¬ (3 : ℤ) ∣ 4 ^ 2 ^ (a - 1) + 1 := fun h ↦
  absurd (prime_eq_of_dvd_sub_one_of_dvd_cyclotomic_eval_pow (ρ := 3) (y := 4) (by norm_num)
    Nat.prime_two ha (by norm_num) (by norm_num) (by simpa [cyclotomic_two] using h))
    (by norm_num)

-- The hypothesis `ρ ∣ y - 1` cannot be dropped: `7 ∣ Φ_3(2) = 7` and `7 ≠ 3`, but `7 ∤ 2 - 1`.
example : (7 : ℤ) ∣ (cyclotomic 3 ℤ).eval (2 ^ 3 ^ (1 - 1)) ∧ ¬ (7 : ℤ) ∣ 2 - 1 := by
  norm_num [cyclotomic_three]

end MathlibExtTest.CommonPrimeDivisorEvalPow
