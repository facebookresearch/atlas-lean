/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.LuriaDelbruck

/-!
# Tests for the Luria–Delbrück distribution

Non-vacuity witness: for `m = 2` the probabilities are nonnegative and sum to `1`. Explicit
values: `P(size = 1) = 1/2`, `P(size = 2) = 1/6`, `p₁ = m e^{-m} / 2`, `p₂ = e^{-m} (m / 6 +
m² / 8)`, and the Ma–Sandri–Sarkar recursion at `n = 1`. The `p₀` method recovers `m = 2`.
Boundary case: `m = 0` puts all mass at `0`.
-/

@[expose] public section

open Finset Real

namespace MathlibExtTest.Biology.PopulationGenetics.LuriaDelbruck

open MathlibExt.Biology.PopulationGenetics.LuriaDelbruck

example : cloneProb 1 = 1 / 2 := by norm_num [cloneProb]
example : cloneProb 2 = 1 / 6 := by norm_num [cloneProb]
example : cloneProb 0 = 0 := by simp [cloneProb]

-- Non-vacuity witness: `m = 2` gives a probability law on `ℕ`.
example (n : ℕ) : 0 ≤ ldPmf 2 n := ldPmf_nonneg (by norm_num) n
example : HasSum (ldPmf 2) 1 := hasSum_ldPmf (by norm_num)

-- `p₁ = m e^{-m} / 2`.
example (m : ℝ) : ldPmf m 1 = m * exp (-m) / 2 := by
  simp [ldPmf, convPow, cloneProb, Finset.sum_range_succ]
  ring

-- `p₂ = e^{-m} (m / 6 + m² / 8)`.
example (m : ℝ) : ldPmf m 2 = exp (-m) * (m / 6 + m ^ 2 / 8) := by
  simp [ldPmf, convPow, cloneProb, Finset.sum_range_succ]
  norm_num
  ring

-- The recursion at `n = 1`: `p₁ = m p₀ / 2`.
example (m : ℝ) : ldPmf m 1 = m / 1 * (ldPmf m 0 / (1 - 0 + 1)) := by
  have := ldPmf_recursion m (n := 1) le_rfl
  simpa using this

-- The `p₀` method recovers the mutation number.
example : -log (ldPmf 2 0) = 2 := (p0_method 2).symm

-- Boundary `m = 0`: no mutants with probability `1`.
example : ldPmf 0 0 = 1 := by simp [ldPmf_zero]
example : ldPmf 0 1 = 0 := by simp [ldPmf, convPow, cloneProb, Finset.sum_range_succ]

end MathlibExtTest.Biology.PopulationGenetics.LuriaDelbruck
