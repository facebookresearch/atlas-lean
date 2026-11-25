/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Shor

@[expose] public section

/-!
# Tests for the continued-fraction step of Shor's order finding

The hypotheses are jointly satisfiable. The numbers follow Shor's Figure 5.1
(`q = 256`, order `r = 10`): with `n = 16` we have `n ^ 2 = q`, and the observed
value `c = 77` satisfies `|77 / 256 - 3 / 10| ≤ 1 / 512`.
-/

namespace Cslib.Shor.Tests

/-- `3 / 10` is a convergent of `77 / 256`. -/
example : ∃ k, ((3 : ℤ) : ℚ) / ((10 : ℕ) : ℚ) = ((77 : ℝ) / 256).convergent k :=
  exists_convergent_eq_of_abs_sub_le ((77 : ℝ) / 256) (q := 256) (n := 16) (r := 10) (d := 3)
    (by norm_num) (by norm_num) (by norm_num) (by rw [abs_le]; norm_num)

/-- Uniqueness: any `d' / r'` with `0 < r' < 16` within `1 / 512` of `77 / 256` equals
`3 / 10`. -/
example (d' : ℤ) (r' : ℕ) (hr' : 0 < r') (hr'n : r' < 16)
    (h' : |(77 : ℝ) / 256 - d' / r'| ≤ 1 / (2 * (256 : ℕ))) :
    ((3 : ℤ) : ℝ) / ((10 : ℕ) : ℝ) = d' / r' :=
  eq_of_abs_sub_le_of_lt ((77 : ℝ) / 256) (q := 256) (n := 16) (by norm_num) (by norm_num) hr'
    (by norm_num) hr'n (by rw [abs_le]; norm_num) h'

/-- The bound `n ^ 2 ≤ q` matters: with `q = 16` and `n = 16` the fractions `1 / 3` and
`4 / 11` are both within `1 / 32` of `0.35`, and they differ. -/
example : |(0.35 : ℝ) - ((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ)| ≤ 1 / (2 * (16 : ℕ)) ∧
    |(0.35 : ℝ) - ((4 : ℤ) : ℝ) / ((11 : ℕ) : ℝ)| ≤ 1 / (2 * (16 : ℕ)) ∧
    ((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ) ≠ ((4 : ℤ) : ℝ) / ((11 : ℕ) : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le]; norm_num
  · rw [abs_le]; norm_num
  · norm_num

end Cslib.Shor.Tests
