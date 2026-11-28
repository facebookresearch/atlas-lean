/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.LucasWeightedPowerSumParameterBound

/-! # Tests for the parameter bound for weighted Lucas power sums -/

open MetaMathlibExt

-- Fibonacci numbers: `1 + 2 + 6 = 3²`, at the first possible cutoff `k = 3`.
example : (fibonacciLucasParams.p : ℚ) ≤ ((3 : ℚ) + 1) ^ 2 / 4 + 1 :=
  le_of_weighted_power_sum_eq fibonacciLucasParams (n := 4) (k := 3) (p := 1) (q := 2)
    (Or.inr rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- For `(x, y) = (2, 1)`, `U_j = j`; the sum of squares through `k = 4` is `U_30`.
example : ((⟨2, 1, by decide⟩ : LucasSequenceParams).p : ℚ) ≤ ((4 : ℚ) + 1) ^ 2 / 4 + 1 :=
  le_of_weighted_power_sum_eq ⟨2, 1, by decide⟩ (n := 30) (k := 4) (p := 1) (q := 1)
    (Or.inl rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- At `k = 3`, the bound rules out all positive indices and exponents for `(x, y) = (6, 1)`.
example {n p q : ℕ} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) :
    ∑ j ∈ Finset.Icc (1 : ℕ) 3, (j : ℤ) * lucasU ⟨6, 1, by decide⟩ j ^ p ≠
      lucasU ⟨6, 1, by decide⟩ n ^ q := by
  intro h
  have hb := le_of_weighted_power_sum_eq ⟨6, 1, by decide⟩ (Or.inl rfl) (by decide)
    hn hp hq (by decide : 3 ≤ 3) h
  exact (by norm_num : ¬ ((6 : ℚ) ≤ ((3 : ℚ) + 1) ^ 2 / 4 + 1)) hb

-- With `k = 1`, the equation alone does not bound `x`.
example :
    (∑ j ∈ Finset.Icc (1 : ℕ) 1, (j : ℤ) * lucasU ⟨5, -1, by decide⟩ j ^ 1) =
      lucasU ⟨5, -1, by decide⟩ 1 ^ 1 ∧ ¬ ((5 : ℚ) ≤ ((1 : ℚ) + 1) ^ 2 / 4 + 1) := by
  exact ⟨by decide, by norm_num⟩
