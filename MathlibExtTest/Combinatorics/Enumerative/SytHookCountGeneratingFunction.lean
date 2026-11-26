/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SytHookCountGeneratingFunction

open MetaMathlibExt PowerSeries

-- The constant term of the Motzkin series is `m_0 = 1`.
private theorem constantCoeff_motzkinSeries : constantCoeff motzkinSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, motzkinSeries, coeff_mk, motzkinNumber_zero,
    Nat.cast_one]

-- Comparing coefficients of `x ^ (n + k + 1)`: two consecutive counts add up to a coefficient of
-- a power of the Motzkin series.
private theorem consecutive_add (n k : ℕ) :
    (sytHookCount (n + k + 1) k : ℤ) + sytHookCount (n + k) k =
      coeff n (motzkinSeries ^ (k + 1)) := by
  have h := congrArg (coeff (n + k + 1)) (sytHookCount_generatingFunction k)
  rw [show n + k + 1 = n + 1 + k by omega, coeff_X_pow_mul, add_mul, one_mul, map_add, map_add,
    coeff_one, ite_eq_right n.succ_ne_zero, zero_add, coeff_succ_X_mul,
    show n + 1 + k = n + k + 1 by omega, coeff_succ_X_mul, coeff_mk, coeff_mk,
    ite_eq_left (by omega), ite_eq_left (by omega)] at h
  exact h

-- The lowest coefficient counts the single-row tableau.
private theorem diagonal (k : ℕ) : sytHookCount k k = 1 := by
  have h := congrArg (coeff k) (sytHookCount_generatingFunction k)
  rw [coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, add_mul, one_mul, map_add, map_add,
    coeff_zero_X_mul, add_zero, coeff_one, ite_eq_left rfl] at h
  cases k with
  | zero => simpa using h
  | succ k =>
    rw [coeff_succ_X_mul, coeff_mk, coeff_mk, ite_eq_left le_rfl, ite_eq_right (by omega),
      add_zero] at h
    exact_mod_cast h

-- No tableau of order `k + 1` has row difference `k`.
private theorem succ_diagonal (k : ℕ) : sytHookCount (k + 1) k = 0 := by
  have h := consecutive_add 0 k
  rw [zero_add, diagonal, coeff_zero_eq_constantCoeff_apply, map_pow,
    constantCoeff_motzkinSeries, one_pow, Nat.cast_one] at h
  omega

-- At order `k + 2` only the shape `(k + 1, 1)` is left, with its `k + 1` tableaux.
example (k : ℕ) : sytHookCount (k + 2) k = k + 1 := by
  have h := consecutive_add 1 k
  rw [show 1 + k + 1 = k + 2 by omega, show 1 + k = k + 1 by omega, succ_diagonal,
    coeff_one_pow, constantCoeff_motzkinSeries, one_pow, mul_one, motzkinSeries, coeff_mk,
    motzkinNumber_one] at h
  push_cast at h
  omega

-- For row difference zero, consecutive counts add up to the Motzkin numbers.
example (n : ℕ) : sytHookCount (n + 1) 0 + sytHookCount n 0 = motzkinNumber n := by
  have h := consecutive_add n 0
  rw [add_zero, pow_one, motzkinSeries, coeff_mk] at h
  exact_mod_cast h
