/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Moran

/-! Tests for the Moran model: explicit step probabilities and fixation probabilities, the
boundary states, the stochastic matrix as a concrete (non-vacuous) chain, the first-step
equation and its uniqueness, absorption of the chain, and the diffusion limit. -/

open Real Filter Set
open scoped Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Moran

open MathlibExt.Biology.PopulationGenetics.Moran
open MathlibExt.Biology.PopulationGenetics.Diffusion

/-! ### Step probabilities -/

/-- `N = 4`, `r = 2`, two mutants: up `(4/6)(2/4) = 1/3`, down `(2/6)(2/4) = 1/6`. -/
example : moranUp 2 4 2 = 1 / 3 := by norm_num [moranUp]

example : moranDown 2 4 2 = 1 / 6 := by norm_num [moranDown]

/-- The down/up ratio is `1 / r`. -/
example : 2 * moranDown 2 4 2 = moranUp 2 4 2 := mul_moranDown 2 4 2

/-- The absorbing states have no up-step at `N` and no down-step at `0`. -/
example : moranUp 3 5 5 = 0 := moranUp_last 3 5

example : moranDown 3 5 0 = 0 := moranDown_zero 3 5

example : moranUp 2 4 2 + moranDown 2 4 2 ≤ 1 :=
  moranUp_add_moranDown_le_one two_pos (by norm_num)

/-! ### The chain as a stochastic matrix (non-vacuity witness) -/

/-- A concrete Moran chain: `N = 2`, `r = 2`. -/
noncomputable example : StochasticMatrix 2 := moranMatrix 2 (r := 2) two_pos

example : (moranMatrix 2 (r := 2) two_pos).prob 1 2 = 1 / 3 := by
  norm_num [moranMatrix, moranProb, moranUp]

example : (moranMatrix 2 (r := 2) two_pos).prob 1 0 = 1 / 6 := by
  norm_num [moranMatrix, moranProb, moranDown]

example : (moranMatrix 2 (r := 2) two_pos).prob 1 1 = 1 / 2 := by
  norm_num [moranMatrix, moranProb, moranUp, moranDown]

/-- The state `N` absorbs. -/
example : (moranMatrix 2 (r := 2) two_pos).prob 2 2 = 1 := by
  norm_num [moranMatrix, moranProb, moranUp, moranDown]

/-! ### Fixation probabilities -/

/-- `N = 2`, `r = 2`, one mutant: `(1 - 1/2) / (1 - 1/4) = 2/3`. -/
example : moranFixation 2 2 1 = 2 / 3 := by norm_num [moranFixation]

/-- Neutral case: `i / N`. -/
example : moranFixation 1 4 1 = 1 / 4 := by norm_num [moranFixation]

/-- A deleterious mutant (`r = 1/2`) is fixed with probability below `1/N`:
`(1 - 2) / (1 - 4) = 1/3 < 1/2`. -/
example : moranFixation (1 / 2) 2 1 = 1 / 3 := by norm_num [moranFixation]

/-- Outside the domain `0 < r` the total definition returns junk: for `r = -1`, `N = 2` the
denominator `1 - (-1) ^ 2` vanishes and Lean's `x / 0 = 0` gives `0`. -/
example : moranFixation (-1) 2 1 = 0 := by norm_num [moranFixation]

example : moranFixation 3 7 0 = 0 := moranFixation_zero 3 7

example : moranFixation 3 7 7 = 1 := moranFixation_self (by norm_num) (by norm_num)

example : moranFixation 1 7 7 = 1 := moranFixation_self one_pos (by norm_num)

example : moranFixation 2 2 1 = moranUp 2 2 1 * moranFixation 2 2 2
    + moranDown 2 2 1 * moranFixation 2 2 0
    + (1 - moranUp 2 2 1 - moranDown 2 2 1) * moranFixation 2 2 1 :=
  moranFixation_eq_firstStep two_pos one_pos

/-- Uniqueness pins down every solution of the first-step problem. -/
example (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (h2 : ψ 2 = 1)
    (hψ : ∀ i, 0 < i → i < 2 → ψ i = moranUp 2 2 i * ψ (i + 1) + moranDown 2 2 i * ψ (i - 1)
      + (1 - moranUp 2 2 i - moranDown 2 2 i) * ψ i) :
    ψ 1 = 2 / 3 := by
  rw [eq_moranFixation two_pos (by norm_num) h0 h2 hψ 1 (by norm_num)]
  norm_num [moranFixation]

/-! ### Absorption of the chain -/

example : Tendsto (fun t => (moranMatrix 2 (r := 2) two_pos).matPow t 1 (Fin.last 2)) atTop
    (𝓝 (2 / 3)) := by
  have h := tendsto_matPow_moranMatrix_last (r := 2) two_pos (N := 2) (by norm_num) 1
  norm_num [moranFixation] at h
  exact h

example : Tendsto (fun t => (moranMatrix 2 (r := 2) two_pos).matPow t 1 0) atTop
    (𝓝 (1 / 3)) := by
  have h := tendsto_matPow_moranMatrix_zero (r := 2) two_pos (N := 2) (by norm_num) 1
  norm_num [moranFixation] at h
  exact h

/-! ### Diffusion limit -/

example : kimuraFixation (2 / 2) (1 / 2) = (1 - exp (-2 * (1 / 2))) / (1 - exp (-2)) :=
  kimuraFixation_half two_ne_zero _

example : Tendsto (fun N : ℕ => moranFixation (1 + 2 / N) N ⌊(1 / 2 : ℝ) * N⌋₊) atTop
    (𝓝 ((1 - exp (-1)) / (1 - exp (-2)))) := by
  have h := tendsto_moranFixation_diffusion 2 (x := 1 / 2) (by norm_num)
  rw [kimuraFixation_half two_ne_zero] at h
  norm_num at h
  exact h

/-- Neutral diffusion limit: `⌊x N⌋ / N → x`. -/
example : Tendsto (fun N : ℕ => moranFixation (1 + 0 / N) N ⌊(1 / 3 : ℝ) * N⌋₊) atTop
    (𝓝 (1 / 3)) := by
  simpa using tendsto_moranFixation_diffusion 0 (x := 1 / 3) (by norm_num)

#print axioms moranMatrix
#print axioms eq_moranFixation
#print axioms tendsto_matPow_moranMatrix_last
#print axioms tendsto_moranFixation_diffusion

end MathlibExtTest.Biology.PopulationGenetics.Moran
