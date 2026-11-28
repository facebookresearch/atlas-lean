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

The mean divided by `log n` tends to `e^{-γ}`, and in particular the mean tends to infinity.

The variance test checks power decay of the normalized error from the Buchstab integral
for every `n ≥ 1`, including the one-point case where the variance is zero.
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

/-- The mean of the smallest cycle length divided by `log n` tends to `e^{-γ}`. -/
example : Filter.Tendsto (fun n : ℕ =>
    ((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ)) /
      (n.factorial : ℝ)) / Real.log n) Filter.atTop
    (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := smallest_cycle_mean_asymp.const_mul (Real.exp (-Real.eulerMascheroniConstant))
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  field_simp

/-- The mean of the smallest cycle length tends to infinity. -/
example : Filter.Tendsto (fun n : ℕ =>
    (∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ)) /
      (n.factorial : ℝ)) Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun n : ℕ =>
      Real.exp (-Real.eulerMascheroniConstant) * Real.log n) Filter.atTop Filter.atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (Real.exp_pos _)
  refine (smallest_cycle_mean_asymp.pos_mul_atTop one_pos hlog).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  field_simp

-- On one point the variance is zero; for every positive `n` the normalized error has power decay.
example (ω : ℝ → ℝ) (h₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (h₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t) :
    ∃ ε C : ℝ, 0 < ε ∧ |2 * ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ 2| ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        |((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ) ^ 2) /
                (n.factorial : ℝ) -
              ((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ)) /
                (n.factorial : ℝ)) ^ 2) / n -
          2 * ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ 2| ≤ C * (n : ℝ) ^ (-ε) := by
  obtain ⟨ε, C, hε, h⟩ := smallest_cycle_variance_asymp ω h₁ h₂
  refine ⟨ε, C, hε, ?_, fun n hn ↦ ?_⟩
  · simpa [Function.minimalPeriod_eq_one_of_subsingleton] using h 1 le_rfl
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_sub' hn'.ne', abs_div, abs_of_pos hn', div_le_iff₀ hn']
    simpa [mul_comm, mul_left_comm, mul_assoc] using h n hn

end MetaMathlibExt.SmallestCycleMomentTest
