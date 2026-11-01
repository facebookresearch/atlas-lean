/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.StickyKernel
public import MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-!
# Tests for the sticky (equal-input) kernel

Non-vacuity witness: `π = (1/2, 1/3, 1/6)` on three states with persistence `1/2` gives a
row-stochastic, `π`-reversible kernel. Explicit entries, the composition law at concrete
values, the boundary persistences `0` and `1`, and a persistence outside `[0, 1]` (`c = 2`) with
a negative entry documenting the domain. The F81 model of `SubstitutionModels` is the
equal-input generator on four bases (with `∑ π = 1`), so its transition function is the sticky
kernel. The two-state ancestry covariance at `α = 1/2`, `r = 0`.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.StickyKernel

/-- A probability vector on three states. -/
noncomputable def π3 : Fin 3 → ℝ := ![1 / 2, 1 / 3, 1 / 6]

theorem π3_nonneg (i : Fin 3) : 0 ≤ π3 i := by fin_cases i <;> norm_num [π3]

theorem π3_sum : ∑ i, π3 i = 1 := by norm_num [π3, Fin.sum_univ_three]

-- Non-vacuity witness: a genuine stochastic, reversible kernel.
example : stickyKernel π3 (1 / 2) ∈ rowStochastic ℝ (Fin 3) :=
  stickyKernel_mem_rowStochastic π3_nonneg π3_sum (by norm_num) (by norm_num)
example : π3 ᵥ* stickyKernel π3 (1 / 2) = π3 := vecMul_stickyKernel π3_sum _
example (i j : Fin 3) : π3 i * stickyKernel π3 (1 / 2) i j = π3 j * stickyKernel π3 (1 / 2) j i :=
  stickyKernel_reversible π3 _ i j

-- Explicit entries: stay with probability `1/2 + 1/2 · 1/2`, move to state 2 w.p. `1/2 · 1/6`.
example : stickyKernel π3 (1 / 2) 0 0 = 3 / 4 := by
  norm_num [stickyKernel_apply, π3]
example : stickyKernel π3 (1 / 2) 0 2 = 1 / 12 := by
  norm_num [stickyKernel_apply, π3]

-- Two steps at persistence `1/2` are one step at persistence `1/4`.
example : stickyKernel π3 (1 / 2) ^ 2 = stickyKernel π3 (1 / 4) := by
  rw [stickyKernel_pow π3_sum]; norm_num

-- Boundary persistences.
example : stickyKernel π3 1 = 1 := stickyKernel_one π3
example (i : Fin 3) : stickyKernel π3 0 i 1 = 1 / 3 := by simp [π3]

-- Outside `[0, 1]` the matrix is still defined but not stochastic: a negative entry.
example : stickyKernel π3 2 0 1 = -1 / 3 := by norm_num [stickyKernel_apply, π3]

-- The equal-input generator is a rate matrix.
example : IsRateMatrix (equalInputRate π3 2) :=
  isRateMatrix_equalInputRate π3_nonneg π3_sum (by norm_num)

open MathlibExt.Biology.Phylogenetics.SubstitutionModels in
/-- F81 (Felsenstein 1981) on four bases is the equal-input generator with rate `1`. -/
theorem f81Rate_eq_equalInputRate {π : Fin 4 → ℝ} (hπ : ∑ i, π i = 1) :
    f81Rate π = equalInputRate π 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [f81Rate, gtrRate, equalInputRate, hπ]
  · simp [f81Rate, gtrRate, equalInputRate, h]

open MathlibExt.Biology.Phylogenetics.SubstitutionModels in
-- Hence the F81 transition function is the sticky kernel with persistence `e^{-t}`.
example {π : Fin 4 → ℝ} (hπ : ∑ i, π i = 1) (t : ℝ) :
    ctmcTransition (f81Rate π) t = stickyKernel π (Real.exp (-t)) := by
  rw [f81Rate_eq_equalInputRate hπ, ctmcTransition_equalInputRate hπ, one_mul]

-- Two-state ancestry covariance at `α = 1/2` and no recombination: `1/4`.
example : (∑ i, ∑ j, ![1 / 2, 1 - 1 / 2] i * stickyKernel ![1 / 2, 1 - 1 / 2] ((1 - 0) ^ 3) i j *
      (![(1 : ℝ), 0] i * ![(1 : ℝ), 0] j) -
      (∑ i, ![1 / 2, 1 - 1 / 2] i * ![(1 : ℝ), 0] i) *
        (∑ j, ![1 / 2, 1 - 1 / 2] j * ![(1 : ℝ), 0] j)) = 1 / 4 := by
  rw [covariance_indicator_stickyKernel_two]; norm_num

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.StickyKernel
