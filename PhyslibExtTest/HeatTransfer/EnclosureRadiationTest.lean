/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.HeatTransfer.EnclosureRadiation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Black enclosure fixtures

Concrete enclosures for `PhyslibExt.HeatTransfer.EnclosureRadiation`: two unequal
surfaces, and an aperture kept as an explicit environment node (deleting it breaks
the enclosure row sums).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

- The two-surface data form a black enclosure with the expected net powers.
- The aperture fixture is a black enclosure, and deleting the aperture node is not.

## iii. Table of contents

- A. Two-surface enclosure
- B. Aperture as an environment node

## iv. References

- `PhyslibExt.HeatTransfer.EnclosureRadiation`.

## A. Two-surface enclosure
-/

namespace HeatTransfer.EnclosureRadiation

/- Two surfaces with unequal areas `A = (1, 2)` and view factors `F = [[0, 1], [1/2, 1/2]]`
(a flat surface facing a concave one) form a black enclosure. -/
example :
    IsBlackEnclosure (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]] := by
  constructor
  · intro i
    fin_cases i
    · simp
    · simp
  · intro i j
    fin_cases i
    · fin_cases j
      · simp
      · simp
    · fin_cases j
      · simp
      · simp
  · intro i
    fin_cases i
    · simp [Fin.sum_univ_two]
    · simp only [Fin.sum_univ_two]
      norm_num
  · intro i j
    fin_cases i
    · fin_cases j
      · simp
      · simp
    · fin_cases j
      · simp
      · simp

/- Two-surface values at `T = (400, 300)`: the hotter surface sends out
`σ * (400 ^ 4 - 300 ^ 4) = 17500000000 * σ`, the cooler one receives the same power, and the
fluxes differ by the area ratio, so fluxes do not cancel. -/
example (σ : ℝ) :
    netPower σ (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]] ![400, 300] 0 =
        17500000000 * σ ∧
      netPower σ (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]] ![400, 300] 1 =
        -17500000000 * σ ∧
      netFlux σ (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]] ![400, 300] 0 =
        17500000000 * σ ∧
      netFlux σ (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]] ![400, 300] 1 =
        -8750000000 * σ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [netPower, Fin.sum_univ_two]
    norm_num
    ring
  · simp [netPower, Fin.sum_univ_two]
    norm_num
    ring
  · simp [netFlux, netPower, Fin.sum_univ_two]
    norm_num
    ring
  · simp [netFlux, netPower, Fin.sum_univ_two]
    norm_num
    ring

/- Aperture as an explicit environment node: surfaces of areas `1` and `2` and an opening of
area `1` (node `2`) with `F = [[0, 1/2, 1/2], [1/4, 1/2, 1/4], [1/2, 1/2, 0]]` form a black
enclosure. -/
example :
    IsBlackEnclosure (![1, 2, 1] : Fin 3 → ℝ)
      ![![0, 1 / 2, 1 / 2], ![1 / 4, 1 / 2, 1 / 4], ![1 / 2, 1 / 2, 0]] := by
  constructor
  · intro i
    fin_cases i
    · simp
    · simp
    · simp
  · intro i j
    fin_cases i
    · fin_cases j
      · simp
      · simp
      · simp
    · fin_cases j
      · simp
      · simp
      · simp
    · fin_cases j
      · simp
      · simp
      · simp
  · intro i
    fin_cases i
    · simp only [Fin.sum_univ_three]
      norm_num
    · simp only [Fin.sum_univ_three]
      norm_num
    · simp only [Fin.sum_univ_three]
      norm_num
  · intro i j
    fin_cases i
    · fin_cases j
      · simp
      · simp
        norm_num
      · simp
    · fin_cases j
      · simp
        norm_num
      · simp
      · simp
        norm_num
    · fin_cases j
      · simp
      · simp
        norm_num
      · simp

/- Invalid: deleting the aperture node leaves the two surfaces with view-factor rows `1/2` and
`3/4`, so the remaining data is not a black enclosure. -/
example :
    ¬ IsBlackEnclosure (![1, 2] : Fin 2 → ℝ) ![![0, 1 / 2], ![1 / 4, 1 / 2]] := by
  intro h
  have h0 := h.rowSum_eq_one 0
  simp [Fin.sum_univ_two] at h0

end HeatTransfer.EnclosureRadiation
