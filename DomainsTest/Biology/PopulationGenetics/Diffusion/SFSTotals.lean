/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Diffusion.SFSTotals

/-! Tests for the neutral site-frequency-spectrum totals: the empty harmonic sums at sample
sizes `0` and `1`, the singleton harmonic sum at sample size `2` (including the degenerate
`θ = 0` scaling), a two-class harmonic sum at sample size `3`, and the pairwise-diversity
totals at sample sizes `2` and `3`. -/

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SFSTotals

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Empty harmonic total: no segregating classes in an empty sample. -/
example (θ : ℝ) : ∑ i ∈ Finset.Ico 1 0, expectedSFS θ 0 0 i = 0 := by
  rw [sum_expectedSFS_neutral,
    Finset.Ico_eq_empty_of_le (by norm_num : (0 : ℕ) ≤ 1), Finset.sum_empty, mul_zero]

/-- Empty harmonic total: no segregating classes in a sample of one. -/
example (θ : ℝ) : ∑ i ∈ Finset.Ico 1 1, expectedSFS θ 0 1 i = 0 := by
  rw [sum_expectedSFS_neutral,
    Finset.Ico_eq_empty_of_le (by norm_num : (1 : ℕ) ≤ 1), Finset.sum_empty, mul_zero]

/-- Singleton harmonic total: the only class is `i = 1`, so the total is `θ`. -/
example (θ : ℝ) : ∑ i ∈ Finset.Ico 1 2, expectedSFS θ 0 2 i = θ := by
  have hIco : Finset.Ico 1 2 = {1} := by decide
  rw [sum_expectedSFS_neutral, hIco, Finset.sum_singleton]
  simp

/-- Two-class harmonic total: `θ * (1 + 1 / 2) = θ * 3 / 2`. -/
example (θ : ℝ) : ∑ i ∈ Finset.Ico 1 3, expectedSFS θ 0 3 i = θ * 3 / 2 := by
  have hIco : Finset.Ico 1 3 = {1, 2} := by decide
  have h12 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
  rw [sum_expectedSFS_neutral, hIco, Finset.sum_insert h12, Finset.sum_singleton]
  norm_num
  ring

/-- Pairwise-diversity total in a sample of two. -/
example (θ : ℝ) :
    ∑ i ∈ Finset.Ico 1 (2 : ℕ),
        (2 * (i : ℝ) * ((2 : ℝ) - (i : ℝ)) / ((2 : ℝ) * ((2 : ℝ) - 1)))
          * expectedSFS θ 0 2 i = θ := by
  simpa using sum_pairwiseDiversity_expectedSFS_neutral θ 2 (by norm_num)

/-- Pairwise-diversity total in a sample of three. -/
example (θ : ℝ) :
    ∑ i ∈ Finset.Ico 1 (3 : ℕ),
        (2 * (i : ℝ) * ((3 : ℝ) - (i : ℝ)) / ((3 : ℝ) * ((3 : ℝ) - 1)))
          * expectedSFS θ 0 3 i = θ := by
  simpa using sum_pairwiseDiversity_expectedSFS_neutral θ 3 (by norm_num)

/-- Degenerate scaling: at `θ = 0` the singleton harmonic total vanishes. -/
example : ∑ i ∈ Finset.Ico 1 2, expectedSFS 0 0 2 i = 0 := by
  rw [sum_expectedSFS_neutral]
  simp

#print axioms sum_expectedSFS_neutral
#print axioms sum_pairwiseDiversity_expectedSFS_neutral

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SFSTotals
