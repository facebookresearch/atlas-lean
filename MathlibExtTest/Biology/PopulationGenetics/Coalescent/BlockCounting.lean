/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.BlockCounting

/-!
# Tests for Kingman's lineage-count limit and Tavaré's formula

Concrete Wright–Fisher lineage-count probabilities (`M = 10`, two lineages), the `M = 0`
junk value, entries of the block-counting generator, Tavaré's formula for two lineages
(`P(2 → 2) = e^{-t}`, `P(2 → 1) = 1 - e^{-t}`), the matrix exponential at `t = 0`, and an
instance of Kingman's limit.
-/

@[expose] public section

open Filter Topology Matrix

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.BlockCounting

open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting

/-- Two lineages in a population of `10` copies coalesce with probability `1/10`. -/
example : wfLineageProb 10 2 1 = 1 / 10 := by
  norm_num [wfLineageProb, Nat.stirlingSecond, Nat.descFactorial]

/-- Two lineages in a population of `10` copies stay distinct with probability `9/10`. -/
example : wfLineageProb 10 2 2 = 9 / 10 := by
  norm_num [wfLineageProb, Nat.stirlingSecond, Nat.descFactorial]

/-- The row of two lineages sums to `1` (`M = 10`). -/
example : wfLineageProb 10 2 0 + wfLineageProb 10 2 1 + wfLineageProb 10 2 2 = 1 := by
  norm_num [wfLineageProb, Nat.stirlingSecond, Nat.descFactorial]

/-- More ancestors than descendants is impossible. -/
example (M : ℕ) : wfLineageProb M 1 2 = 0 := by
  simp [wfLineageProb, Nat.stirlingSecond]

/-- Boundary `M = 0` (outside the model): the totalized `0 / 0 = 0` gives a row of zeros. -/
example : wfLineageProb 0 1 1 = 0 := by
  simp [wfLineageProb]

/-- Generator entries for two lineages: rate `1` to one lineage, `-1` on the diagonal. -/
example : blockCountingGenerator 2 2 1 = 1 ∧ blockCountingGenerator 2 2 2 = -1 := by
  constructor <;> simp [blockCountingGenerator]

/-- One lineage is absorbing: row `1` of the generator is zero. -/
example (j : Fin 3) : blockCountingGenerator 2 1 j = 0 := by
  fin_cases j <;> simp [blockCountingGenerator]

/-- Tavaré's closed form for two lineages staying two: `e^{-t}`. -/
example (t : ℝ) : tavareProb 2 2 t = Real.exp (-t) := by
  simp [tavareProb, Nat.ascFactorial, Nat.descFactorial, Nat.factorial]
  ring_nf

/-- Tavaré's closed form for two lineages coalescing to one: `1 - e^{-t}`. -/
example (t : ℝ) : tavareProb 2 1 t = 1 - Real.exp (-t) := by
  rw [tavareProb, show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)]
  simp [Nat.ascFactorial, Nat.descFactorial, Nat.factorial]
  ring_nf

/-- Tavaré's formula applied: `exp (t • G) 2 1 = 1 - e^{-t}` for the generator on `{0, 1, 2}`. -/
example (t : ℝ) : NormedSpace.exp (t • blockCountingGenerator 2) 2 1 = 1 - Real.exp (-t) := by
  rw [exp_blockCountingGenerator_apply 2 t 2 1 (by decide) (by decide)]
  change tavareProb 2 1 t = _
  rw [tavareProb, show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)]
  simp [Nat.ascFactorial, Nat.descFactorial, Nat.factorial]
  ring_nf

/-- At `t = 0` Tavaré's formula gives the identity: `P(3 → 3) = 1`. -/
example : tavareProb 3 3 0 = 1 := by
  simp [tavareProb, Nat.ascFactorial, Nat.descFactorial, Nat.factorial]
  norm_num

/-- Kingman's limit for samples of at most three lineages after `⌊M / 2⌋` generations. -/
example : Tendsto (fun M : ℕ => wfLineageMatrix 3 M ^ ⌊(1 / 2 : ℝ) * M⌋₊) atTop
    (𝓝 (NormedSpace.exp ((1 / 2 : ℝ) • blockCountingGenerator 3))) :=
  tendsto_wfLineageMatrix_pow_floor 3 (by norm_num)

/-- The eigenvector matrices are inverse to each other (`n = 2`). -/
example : blockCountingLeftEigen 2 * blockCountingRightEigen 2 = 1 :=
  blockCountingLeftEigen_mul_rightEigen 2

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.BlockCounting
