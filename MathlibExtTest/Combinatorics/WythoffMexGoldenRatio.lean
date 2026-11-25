/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WythoffMexGoldenRatio

open scoped goldenRatio

namespace MetaMathlibExt.WythoffMexGoldenRatioTest

-- At the smallest permitted terminal level, the correction changes at the second pair.
example : ∃ lam : ℕ → ℤ, lam 0 = 1 ∧ lam 1 = 0 ∧ ∀ n,
    (wythoffMexB 1 n : ℤ) = ⌊((n + 1 : ℕ) : ℝ) * φ ^ 2⌋ + lam n + 1 := by
  have hfloor0 : ⌊φ⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · simpa using Real.one_lt_goldenRatio.le
    · norm_num
      exact Real.goldenRatio_lt_two
  have hfloor1 : ⌊(2 : ℝ) * φ⌋ = 3 := by
    have hs : (2 : ℝ) ≤ Real.sqrt 5 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    rw [Int.floor_eq_iff]
    constructor
    · norm_num [Real.goldenRatio]
      linarith
    · norm_num
      linarith [Real.goldenRatio_lt_two]
  obtain ⟨lam, _, hformula⟩ := wythoffMex_floor_goldenRatio 1 (by decide)
  have h0 := (hformula 0).1
  have h1 := (hformula 1).1
  norm_num [wythoffMexA_zero, hfloor0] at h0
  norm_num [wythoffMexA_one, hfloor1] at h1
  exact ⟨lam, by omega, by omega, fun n => (hformula n).2⟩

end MetaMathlibExt.WythoffMexGoldenRatioTest
