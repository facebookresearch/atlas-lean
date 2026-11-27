/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryFortyOne

open MetaMathlibExt

-- Zero is exactly the exponent for which every prime factor lies in the excluded set.
example (g : ℕ) :
    (∀ q : ℕ, q.Prime → q ∣ sigmaBiunitary (41 ^ g) → q ∈ ({2, 3, 5, 13} : Finset ℕ)) ↔
      g = 0 := by
  constructor
  · intro h
    by_contra hg
    obtain ⟨q, hq, hdvd, hout⟩ := exists_prime_dvd_sigmaBiunitary_fortyOne_pow g (by omega)
    exact hout (h q hq hdvd)
  · rintro rfl q hq hdvd
    simp [sigmaBiunitary_one, hq.not_dvd_one] at hdvd

-- The first odd and even exponents have witnesses 7 and 29, respectively.
example : sigmaBiunitary 41 = 2 * 3 * 7 := by decide

example : sigmaBiunitary (41 ^ 2) = 2 * 29 ^ 2 := by decide +kernel

-- At exponent two the middle divisor is absent; the first bound is sharp for `p = 2`.
example : (5 / 4 : ℚ) ≤ (sigmaBiunitary (2 ^ 2) : ℚ) / ((2 : ℕ) : ℚ) ^ 2 := by
  have h : (1 : ℚ) + 1 / ((2 : ℕ) : ℚ) ^ 2 = 5 / 4 := by norm_num
  rw [← h]
  exact (sigmaBiunitary_prime_pow_div_ge 2 2 (by decide) (by decide)).1

-- At exponent four the strongest bound is sharp; the proof must omit the middle divisor.
example : (27 / 16 : ℚ) ≤ (sigmaBiunitary (2 ^ 4) : ℚ) / ((2 : ℕ) : ℚ) ^ 4 := by
  have h : (1 + 1 / ((2 : ℕ) : ℚ)) * (1 + 1 / ((2 : ℕ) : ℚ) ^ 3) = 27 / 16 := by norm_num
  rw [← h]
  exact (sigmaBiunitary_prime_pow_div_ge 2 4 (by decide) (by decide)).2.2 (by decide)

-- The second bound includes the first power and is sharp for any prime.
example : (4 / 3 : ℚ) ≤ (sigmaBiunitary (3 ^ 1) : ℚ) / ((3 : ℕ) : ℚ) ^ 1 := by
  have h : (1 : ℚ) + 1 / ((3 : ℕ) : ℚ) = 4 / 3 := by norm_num
  rw [← h]
  exact (sigmaBiunitary_prime_pow_div_ge 3 1 (by decide) (by decide)).2.1 (by decide)
