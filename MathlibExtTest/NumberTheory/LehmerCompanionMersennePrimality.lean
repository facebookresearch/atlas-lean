/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.LehmerCompanionMersennePrimality

/-! # Tests for the Lehmer companion primality criterion -/

open MetaMathlibExt

-- Check the hypotheses and primality directly at the first eligible exponent. Here `R` and `Q`
-- are not coprime, but `Q` is coprime to the Mersenne number.
example : Odd (3 : ℕ) ∧ 3 ≤ (3 : ℕ) ∧ Int.gcd 12 2 = 2 ∧
    Int.gcd (mersenne 3) 2 = 1 ∧ (mersenne 3 : ℤ) ∣ lehmerV 12 2 (2 ^ (3 - 1)) := by
  decide

example : (mersenne 3).Prime := by
  norm_num [mersenne]

-- At the next exponent, 31 divides the term at index 16, but not the term at index 8.
example : Odd (5 : ℕ) ∧ 3 ≤ (5 : ℕ) ∧ Int.gcd (mersenne 5) 1 = 1 ∧
    (mersenne 5 : ℤ) ∣ lehmerV 6 1 (2 ^ (5 - 1)) ∧
    ¬ (mersenne 5 : ℤ) ∣ lehmerV 6 1 (2 ^ (5 - 2)) := by
  decide

example : (mersenne 5).Prime := by
  norm_num [mersenne]

-- The coprimality hypothesis cannot be dropped: the companion term can vanish for composite M₉.
example : Int.gcd (mersenne 9) 0 ≠ 1 ∧
    (mersenne 9 : ℤ) ∣ lehmerV 0 0 (2 ^ (9 - 1)) ∧ ¬ (mersenne 9).Prime := by
  refine ⟨by decide, ?_, by norm_num [mersenne]⟩
  rw [show 2 ^ (9 - 1) = 252 + 4 by decide, lehmerV_add_four]
  simp

example : (mersenne 3).Prime :=
  mersenne_prime_of_dvd_lehmerV (n := 3) (hn := by decide) (h3 := by decide) (R := 12) (Q := 2)
    (hQ := by decide) (hV := by decide)
