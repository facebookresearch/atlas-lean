/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.SiPhy
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/-!
# SiPhy tests

Two states, unit exchangeabilities, constraint vector `π = (1/2, 1/2)`, expected substitution
counts `n = [[0, 3], [1, 0]]` and expected durations `τ = (2, 2)`: the SiPhy matrix is a rate
matrix in detailed balance with `π` (the non-vacuity witness of the model hypotheses), the
rate update is `ω = 4 / 2 = 2`, it beats `ω = 1`, and the hypotheses of the `π` update hold for
`ω = 2` (the update exists). With no substitutions (`n = 0`) the rate update is the junk value `0`,
outside the domain `N > 0`.
-/

namespace MathlibExt.Biology.Phylogenetics.SiPhy

open Matrix ProbabilityTheory

/-- Unit exchangeabilities on two states. -/
def R₂ : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1

/-- Uniform constraint vector. -/
noncomputable def π₂ : Fin 2 → ℝ := fun _ => 1 / 2

/-- Expected substitution counts: `3` of `0 → 1`, `1` of `1 → 0`. -/
def n₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 3; 1, 0]

/-- Expected durations. -/
def τ₂ : Fin 2 → ℝ := fun _ => 2

/-- Root posterior. -/
def r₂ : Fin 2 → ℝ := ![1, 0]

example : IsRateMatrix (siphyRate 2 R₂ π₂) :=
  isRateMatrix_siphyRate (by norm_num) (fun _ _ => by norm_num [R₂]) (fun _ => by norm_num [π₂])

example : IsDetailedBalance π₂ (siphyRate 2 R₂ π₂) :=
  isDetailedBalance_siphyRate 2 (fun _ _ => rfl) π₂

theorem totalCount_n₂ : totalCount n₂ = 4 := by
  norm_num [totalCount, n₂, Fin.sum_univ_two]

theorem denom₂ : ∑ b, exitWeight τ₂ R₂ b * π₂ b = 2 := by
  norm_num [exitWeight, τ₂, R₂, π₂, Fin.sum_univ_two]

example : omegaUpdate n₂ τ₂ R₂ π₂ = 2 := by
  rw [omegaUpdate, totalCount_n₂, denom₂]; norm_num

/-- The update `ω = 2` beats `ω = 1`. -/
example : expectedLogLik n₂ τ₂ r₂ (siphyRate 1 R₂ π₂) π₂ <
    expectedLogLik n₂ τ₂ r₂ (siphyRate (omegaUpdate n₂ τ₂ R₂ π₂) R₂ π₂) π₂ :=
  expectedLogLik_lt_omegaUpdate n₂ τ₂ r₂ (fun _ _ _ => by norm_num [R₂])
    (fun _ => by norm_num [π₂]) (by rw [totalCount_n₂]; norm_num) (by rw [denom₂]; norm_num)
    one_pos (by rw [omegaUpdate, totalCount_n₂, denom₂]; norm_num)

/-- The hypotheses of the constraint-vector update hold here. -/
example : ∀ b, 0 < inCount n₂ r₂ b := by
  intro b; fin_cases b <;> norm_num [inCount, n₂, r₂, Fin.sum_univ_two]

example : ∀ b, 0 ≤ 2 * exitWeight τ₂ R₂ b := by
  intro b; fin_cases b <;> norm_num [exitWeight, τ₂, R₂, Fin.sum_univ_two]

/-- Junk value outside the domain: with no substitutions the update is `0`. -/
example : omegaUpdate 0 τ₂ R₂ π₂ = 0 := by
  simp [omegaUpdate, totalCount]

end MathlibExt.Biology.Phylogenetics.SiPhy
