/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.BinPacking

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-- Boundary check: the bound instantiates for three items packed
feasibly into one bin, giving `nextFit ≤ 2`. -/
example {sizes : List ℝ} (hpos : ∀ x ∈ sizes, 0 < x) (hle : ∀ x ∈ sizes, x ≤ 1)
    {a : ℕ → ℕ} (hfeas : FeasibleAssignment sizes 1 a) :
    nextFitBins sizes ≤ 2 * 1 :=
  nextFit_le_two_mul_opt hpos hle hfeas

/-- The empty list needs no bins: its Next Fit count is `0` by the
defining equation. -/
example : nextFitBins [] = 0 := rfl

/-- Fit branch: `[1/2, 1/4]` fits in a single bin, since `1/2 + 1/4 ≤ 1`. -/
example : nextFitBins [1 / 2, 1 / 4] = 1 := by
  have h : (2 : ℝ)⁻¹ + (4 : ℝ)⁻¹ ≤ 1 := by norm_num
  simp [nextFitBins, nextFitAux, h]

/-- Overflow branch: `[3/4, 3/4]` needs two bins, since `3/4 + 3/4 > 1`. -/
example : nextFitBins [3 / 4, 3 / 4] = 2 := by
  have h : ¬ (3 / 4 : ℝ) + 3 / 4 ≤ 1 := by norm_num
  simp [nextFitBins, nextFitAux, h]

/-- Both branches: `[1/2, 3/4, 1/4]` closes the first bin at `3/4`
(`1/2 + 3/4 > 1`) and then fits `1/4` (`3/4 + 1/4 ≤ 1`), for two bins total. -/
example : nextFitBins [1 / 2, 3 / 4, 1 / 4] = 2 := by
  have h1 : ¬ (2 : ℝ)⁻¹ + 3 / 4 ≤ 1 := by norm_num
  have h2 : (3 / 4 : ℝ) + (4 : ℝ)⁻¹ ≤ 1 := by norm_num
  simp [nextFitBins, nextFitAux, h1, h2]

/-- `[1/2, 1/2, 1/2]` uses two Next Fit bins: the first two items fill one bin
(`1/2 + 1/2 ≤ 1`) and the third overflows (`1 + 1/2 > 1`). -/
example : nextFitBins [1 / 2, 1 / 2, 1 / 2] = 2 := by
  have h1 : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ ≤ 1 := by norm_num
  have h2 : ¬ (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ ≤ 1 := by norm_num
  simp [nextFitBins, nextFitAux, h1, h2]

/-- The assignment sending the first two items to bin `0` and the third to bin `1`
is feasible for `[1/2, 1/2, 1/2]` with `B = 2`: bin `0` holds `1/2 + 1/2 ≤ 1`
and bin `1` holds `1/2 ≤ 1`. -/
theorem half_half_half_feasible :
    FeasibleAssignment [1 / 2, 1 / 2, 1 / 2] 2 (fun i => if i = 2 then 1 else 0) := by
  constructor
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    by_cases h : i = 2 <;> simp [h]
  · intro b hb
    have hb0 : b = 0 ∨ b = 1 := by omega
    rcases hb0 with rfl | rfl
    · have hset : (Finset.range 3).filter (fun i => (if i = 2 then (1 : ℕ) else 0) = 0)
          = {0, 1} := by decide
      change (∑ i ∈ (Finset.range 3).filter (fun i => (if i = 2 then (1 : ℕ) else 0) = 0),
          ([1 / 2, 1 / 2, 1 / 2] : List ℝ).getD i 0) ≤ 1
      rw [hset, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
      norm_num
    · have hset : (Finset.range 3).filter (fun i => (if i = 2 then (1 : ℕ) else 0) = 1)
          = {2} := by decide
      change (∑ i ∈ (Finset.range 3).filter (fun i => (if i = 2 then (1 : ℕ) else 0) = 1),
          ([1 / 2, 1 / 2, 1 / 2] : List ℝ).getD i 0) ≤ 1
      rw [hset, Finset.sum_singleton]
      norm_num

/-- Concrete instance of the bound: the three-half list packs feasibly into two
bins, so Next Fit uses at most four bins. -/
example (hpos : ∀ x ∈ ([1 / 2, 1 / 2, 1 / 2] : List ℝ), 0 < x)
    (hle : ∀ x ∈ ([1 / 2, 1 / 2, 1 / 2] : List ℝ), x ≤ 1) :
    nextFitBins [1 / 2, 1 / 2, 1 / 2] ≤ 2 * 2 :=
  nextFit_le_two_mul_opt hpos hle half_half_half_feasible
