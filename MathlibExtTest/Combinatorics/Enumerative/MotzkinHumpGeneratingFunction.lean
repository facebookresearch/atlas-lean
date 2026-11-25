/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MotzkinHumpGeneratingFunction

namespace MetaMathlibExt

open PowerSeries

-- At the first possible length the path consists of k up steps followed by k down steps.
example (k : ℕ) (hk : 1 ≤ k) : motzkinHumpCount (2 * k) k = 1 := by
  have h := congrArg (coeff (2 * k)) (motzkinHumpCount_generatingFunction k hk)
  rw [sub_mul, one_mul, map_sub, coeff_mk, coeff_X_pow_mul'] at h
  have hd : 2 * k - 1 + 1 = 2 * k := by omega
  rw [← hd, coeff_succ_X_mul, coeff_mk] at h
  simp [hd, show ¬ 2 * k ≤ 2 * k - 1 by omega, motzkinSeries, motzkinNumber_zero] at h
  exact h

-- One step past the cutoff at height two, the increase is four.
example : (motzkinHumpCount 5 2 : ℤ) - motzkinHumpCount 4 2 = 4 := by
  have h := congrArg (coeff 5) (motzkinHumpCount_generatingFunction 2 (by decide))
  rw [sub_mul, one_mul, map_sub, coeff_mk, coeff_succ_X_mul, coeff_mk, coeff_X_pow_mul'] at h
  change (if 4 ≤ 5 then _ else _) - (if 4 ≤ 4 then _ else _) =
    (if 4 ≤ 5 then coeff 1 (motzkinSeries ^ 4) else _) at h
  rw [ite_eq_left (by decide), ite_eq_left (by decide), ite_eq_left (by decide),
    coeff_one_pow] at h
  simp only [motzkinSeries, coeff_mk, motzkinNumber_one, constantCoeff_mk, motzkinNumber_zero,
    Nat.cast_one, one_pow, mul_one] at h
  exact h

end MetaMathlibExt
