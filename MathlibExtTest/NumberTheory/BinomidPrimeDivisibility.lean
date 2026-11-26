/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidPrimeDivisibility

open MetaMathlibExt

/-- The increasing index `0, 1, 2, …` gives infinitely many even inner-coefficient rows. -/
example : {n : ℕ | ∀ k, 1 ≤ k → k < n → ∃ z : ℤ,
    generalizedBinomialCoefficient (fun i => 2 ^ (i - 1)) k (n - k) = (2 : ℚ) * z}.Infinite := by
  apply infinite_setOf_prime_dvd_nomid_of_not_isLexMinimalExtension (μ := id)
    (isBinomidIndex_of_monotone fun _ _ h => h) _ (by decide)
  rintro ⟨m, _, hmin⟩
  -- Truncating the values at m produces a smaller extension of the same prefix.
  let γ (i : ℕ) := min i m
  have hγ : IsBinomidIndex γ := isBinomidIndex_of_monotone fun _ _ h => min_le_min h le_rfl
  rcases hmin γ hγ (fun i hi => min_eq_left hi.le) with heq | ⟨j, _, hlt⟩
  · have h := congrFun heq (m + 1)
    exact Nat.not_succ_le_self m (h.trans_le (min_le_right _ _))
  · exact (not_lt_of_ge (min_le_left j m)) hlt
