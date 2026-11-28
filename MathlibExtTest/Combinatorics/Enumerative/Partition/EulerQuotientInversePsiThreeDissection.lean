/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.EulerQuotientInversePsiThreeDissection
import Mathlib.Tactic.NormNum

open MetaMathlibExt QPochhammer

-- Check the public statement at a nonzero argument inside the unit disk.
example :
    let E : ℕ → ℂ := fun k => if hk : k = 0 then 1 else
      qPochhammerInf ((1 / 2 : ℂ) ^ k) ((1 / 2 : ℂ) ^ k)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (by norm_num) hk)
    E 1 / E 2 ^ 2 =
      E 3 ^ 2 * E 9 ^ 3 / E 6 ^ 6 - (1 / 2 : ℂ) * (E 3 ^ 3 * E 18 ^ 3 / E 6 ^ 7) +
        (1 / 2 : ℂ) ^ 2 * (E 3 ^ 4 * E 18 ^ 6 / (E 6 ^ 8 * E 9 ^ 3)) :=
  eulerFunction_one_div_two_sq_eq (1 / 2) (by norm_num)

-- At zero the correction terms vanish and the leading Euler quotient equals one.
example : qPochhammerInf 0 0 (by simp) / qPochhammerInf 0 0 (by simp) ^ 2 = 1 := by
  have h := eulerFunction_one_div_two_sq_eq 0 (by simp)
  norm_num [qPochhammerInf_zero_left] at h ⊢
