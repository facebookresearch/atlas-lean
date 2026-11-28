/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamanujanTauModSeventeen

open MetaMathlibExt

-- At n = 1 the surviving term uses τ₇(2), exhibiting the shift in the coefficient index.
example : generalizedTau 24 2 ≡ generalizedTau 7 2 [ZMOD 17] := by
  have h := ramanujanTau_succ_modEq_pentagonal_tau_seven 1 one_pos
  simp only [Nat.cast_one] at h
  have indices : (Finset.Icc (-1 : ℤ) 1).filter (fun r => 17 * pentagonal r ≤ 1) =
      {0} := by
    simp only [pentagonal_def]
    decide
  rw [← Finset.sum_filter, indices] at h
  simpa [pentagonal_def] using h

-- At n = 34, the negative index r = -1 contributes -τ₇(1) at the inclusive cutoff.
example : generalizedTau 24 35 ≡ generalizedTau 7 35 - generalizedTau 7 18 - 1 [ZMOD 17] := by
  have h := ramanujanTau_succ_modEq_pentagonal_tau_seven 34 (by decide)
  simp only [Nat.cast_ofNat] at h
  have indices : (Finset.Icc (-34 : ℤ) 34).filter (fun r => 17 * pentagonal r ≤ 34) =
      {-1, 0, 1} := by
    simp only [pentagonal_def]
    decide
  rw [← Finset.sum_filter, indices] at h
  simpa [pentagonal_def, generalizedTau_one, sub_eq_add_neg, add_comm, add_left_comm] using h
