/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.HardyWeinbergExact

import Mathlib.Tactic.NormNum

@[expose] public section

open Finset MathlibExt.Probability.Statistics.ExactTests

namespace MathlibExtTest.Probability.Statistics.ExactTests.HardyWeinbergExact

/-- Two individuals with two `A` alleles: either one `AA` and one `BB` (probability `1/3`) or
two heterozygotes (probability `2/3`). -/
example : leveneProb 2 2 0 = 1 / 3 := by
  norm_num [leveneProb, Nat.factorial]

example : leveneProb 2 2 2 = 2 / 3 := by
  norm_num [leveneProb, Nat.factorial]

/-- Boundary: a heterozygote count of the wrong parity, or exceeding `n_B`, is impossible. -/
example : leveneProb 2 2 1 = 0 := by
  norm_num [leveneProb]

example : leveneProb 2 3 2 = 0 := by
  norm_num [leveneProb]

/-- Boundary: with no `A` allele every individual is `BB`, so `n_AB = 0` surely. -/
example : leveneProb 3 0 0 = 1 := by
  norm_num [leveneProb, Nat.factorial]

/-- Boundary: with only `A` alleles (`n_A = 2N`) every individual is `AA`. -/
example : leveneProb 2 4 0 = 1 := by
  norm_num [leveneProb, Nat.factorial, show Even 4 from ⟨2, rfl⟩]

/-- Outside the domain `n_A ≤ 2N` the definition returns `0`. -/
example : leveneProb 1 3 1 = 0 := by
  norm_num [leveneProb]

/-- Normalization for `N = 2`, `n_A = 2`, directly and from the theorem. -/
example : ∑ h ∈ range 3, leveneProb 2 2 h = 1 := by
  norm_num [Finset.sum_range_succ, leveneProb, Nat.factorial]

example : ∑ h ∈ range 3, leveneProb 2 2 h = 1 := sum_leveneProb (by norm_num)

/-- A larger case: `N = 3` individuals, `n_A = 3`: `P(n_AB = 1) = 3/5` and `P(n_AB = 3) = 2/5`. -/
example : leveneProb 3 3 1 = 3 / 5 := by
  norm_num [leveneProb, Nat.factorial]

example : leveneProb 3 3 3 = 2 / 5 := by
  norm_num [leveneProb, Nat.factorial]

/-- `hetCount`: with the `A` gametes in slots `(0, 0)` and `(1, 0)`, both individuals are
heterozygous; in slots `(0, 0)` and `(0, 1)`, none is. -/
example : hetCount ({(0, 0), (1, 0)} : Finset (Fin 2 × Fin 2)) = 2 := by decide

example : hetCount ({(0, 0), (0, 1)} : Finset (Fin 2 × Fin 2)) = 0 := by decide

/-- The counting model reproduces Levene's formula on an instance. -/
example :
    ((univ.filter fun s : Finset (Fin 2 × Fin 2) => s.card = 2 ∧ hetCount s = 2).card : ℝ) /
      (2 * 2).choose 2 = 2 / 3 := by
  rw [card_hetCount_div_choose]
  norm_num [leveneProb, Nat.factorial]

end MathlibExtTest.Probability.Statistics.ExactTests.HardyWeinbergExact
