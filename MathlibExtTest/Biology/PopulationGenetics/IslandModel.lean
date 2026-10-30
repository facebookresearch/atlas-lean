/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.IslandModel

/-! Tests for Wright's island model: explicit equilibria, the boundary cases `m = 1` (all
migrants), `m = 0` (isolated demes) and `M = 2` (the smallest deme), the out-of-model
algebraic case `M = 1`, a junk value at `M = 0`,
the fixed-point, convergence and uniqueness theorems on concrete parameters, and Wright's
`1 / (1 + 4Nm)` limit. -/

open Filter Set
open scoped Topology

namespace MathlibExtTest.Biology.PopulationGenetics.IslandModel

open MathlibExt.Biology.PopulationGenetics.IslandModel

/-! ### Concrete values -/

/-- Two gene copies per deme and half of them migrants: `F* = (1/4) / (7/4) = 1/7`. -/
example : islandEquilibrium 2 (1 / 2) = 1 / 7 := by
  norm_num [islandEquilibrium]

example : islandStep 2 (1 / 2) (1 / 7) = 1 / 7 := by
  norm_num [islandStep]

/-- One generation from `F = 0` with `M = 10`, `m = 1/10`: `F' = (81/100) · (1/10)`. -/
example : islandStep 10 (1 / 10) 0 = 81 / 1000 := by
  norm_num [islandStep]

/-- Boundary `m = 1`: every gene is a migrant, so nothing is identical by descent. -/
example (M : ℕ) (F : ℝ) : islandStep M 1 F = 0 := by
  simp [islandStep]

example (M : ℕ) : islandEquilibrium M 1 = 0 := by
  simp [islandEquilibrium]

/-- Boundary `m = 0`: isolated demes become completely inbred, `F* = 1`, and the recursion
converges to `1`. -/
example (M : ℕ) : islandEquilibrium M 0 = 1 := islandEquilibrium_zero_right M

example : Tendsto (fun t => (islandStep 4 0)^[t] 0) atTop (𝓝 1) := by
  simpa using tendsto_islandStep_iterate (M := 4) (m := 0) (by norm_num)
    ⟨le_rfl, zero_le_one⟩ 0

example : islandEquilibrium 4 0 ∈ Icc (0 : ℝ) 1 :=
  islandEquilibrium_mem_Icc (by norm_num) ⟨le_rfl, zero_le_one⟩

/-- Outside the domain (`M = 0`, no gene copies) the total definition returns a junk value:
`F* = (1 - m) ^ 2 / (1 - m) ^ 2 = 1` for `m = 1/2`, although no deme exists. -/
example : islandEquilibrium 0 (1 / 2) = 1 := by
  norm_num [islandEquilibrium]

/-- Outside the model (`M = 1`, a single gene copy, so no pair of distinct copies to sample):
the theorems still apply algebraically and give `F* = (1 - m) ^ 2`, which has no biological
meaning. -/
example (m : ℝ) : islandEquilibrium 1 m = (1 - m) ^ 2 := by
  simp [islandEquilibrium]

/-- Boundary of the model `M = 2` (one diploid individual): `F* = (1 - m) ^ 2 / (2 - (1 - m) ^ 2)`.
-/
example (m : ℝ) : islandEquilibrium 2 m = (1 - m) ^ 2 / (2 - (1 - m) ^ 2) := by
  norm_num [islandEquilibrium]

/-! ### The theorems on concrete parameters (hypotheses are satisfiable) -/

example : islandStep 2 (1 / 2) (islandEquilibrium 2 (1 / 2)) = islandEquilibrium 2 (1 / 2) :=
  islandStep_islandEquilibrium (by norm_num) ⟨by norm_num, by norm_num⟩

example (F : ℝ) (hF : islandStep 2 (1 / 2) F = F) : F = 1 / 7 := by
  rw [eq_islandEquilibrium_of_islandStep_eq (by norm_num) ⟨by norm_num, by norm_num⟩ hF]
  norm_num [islandEquilibrium]

example : (islandStep 2 (1 / 2))^[3] 1 - 1 / 7 = (1 / 8) ^ 3 * (1 - 1 / 7) := by
  have h := islandStep_iterate_sub (M := 2) (m := 1 / 2) (by norm_num)
    ⟨by norm_num, by norm_num⟩ 1 3
  norm_num [islandEquilibrium] at h ⊢
  linarith

example : Tendsto (fun t => (islandStep 2 (1 / 2))^[t] 0) atTop (𝓝 (1 / 7)) := by
  have h := tendsto_islandStep_iterate (M := 2) (m := 1 / 2) (by norm_num)
    ⟨by norm_num, by norm_num⟩ 0
  norm_num [islandEquilibrium] at h ⊢
  exact h

example : islandEquilibrium 100 (1 / 100) ∈ Ico (0 : ℝ) 1 :=
  islandEquilibrium_mem_Ico (by norm_num) ⟨by norm_num, by norm_num⟩

/-! ### Wright's limit -/

/-- Scaled migration parameter `4 N m = 1` gives `F_ST → 1/2`. -/
example : Tendsto (fun N : ℕ => islandEquilibrium (2 * N) (1 / (4 * N))) atTop (𝓝 (1 / 2)) := by
  have h := tendsto_islandEquilibrium (κ := 1) zero_le_one
  rwa [show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num] at h

/-- `4 N m = 3` gives `F_ST → 1/4`. -/
example : Tendsto (fun N : ℕ => islandEquilibrium (2 * N) (3 / (4 * N))) atTop (𝓝 (1 / 4)) := by
  have h := tendsto_islandEquilibrium (κ := 3) (by norm_num)
  rwa [show (1 : ℝ) / (1 + 3) = 1 / 4 by norm_num] at h

#print axioms tendsto_islandStep_iterate
#print axioms tendsto_islandEquilibrium

end MathlibExtTest.Biology.PopulationGenetics.IslandModel
