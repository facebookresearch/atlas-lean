/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SmallestCycleMoment

/-!
# Tests for the moments of the shortest permutation cycle

The second moment grows linearly. On one point the unique permutation has moment one,
so the same error constant also bounds the discrepancy there.
-/

namespace MetaMathlibExt.SmallestCycleMomentTest

example (ω : ℝ → ℝ) (h₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (h₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t) :
    ∃ ε C : ℝ, 0 < ε ∧ |1 - 2 * ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ 2| ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        |((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ) ^ 2) /
              (n.factorial : ℝ)) / n - 2 * ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ 2|
          ≤ C * (n : ℝ) ^ (-ε) := by
  obtain ⟨ε, C, hε, h⟩ := smallest_cycle_moment_asymp ω h₁ h₂ 2 le_rfl
  refine ⟨ε, C, hε, ?_, fun n hn ↦ ?_⟩
  · simpa [Function.minimalPeriod_eq_one_of_subsingleton] using h 1 le_rfl
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_sub' hn'.ne', abs_div, abs_of_pos hn', div_le_iff₀ hn']
    simpa [mul_comm, mul_left_comm, mul_assoc] using h n hn

end MetaMathlibExt.SmallestCycleMomentTest
