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
import Mathlib.Tactic.Ring

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
- With emissivities `1/2` the two-surface radiosities solve the gray equations uniquely and the
  net powers are two fifths of the black ones; with emissivities `1` the black values return.

## iii. Table of contents

- A. Two-surface enclosure
- B. Aperture as an environment node
- C. Gray two-surface enclosure

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

/-! ## C. Gray two-surface enclosure -/

/- Two gray surfaces on the black fixture's geometry, areas `A = (1, 2)` and view factors
`F = [[0, 1], [1/2, 1/2]]`, with `ε = (1/2, 1/2)` at `T = (400, 300)`: the radiosities
`J = (18600000000 * σ, 11600000000 * σ)` solve the equations and the net powers are
`± 7000000000 * σ`, two fifths of the black exchange `17500000000 * σ`. -/
example (σ : ℝ) :
    IsRadiosity σ ![1 / 2, 1 / 2] ![![0, 1], ![1 / 2, 1 / 2]] ![400, 300]
        ![18600000000 * σ, 11600000000 * σ] ∧
      grayNetPower (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]]
          ![18600000000 * σ, 11600000000 * σ] 0 = 7000000000 * σ ∧
      grayNetPower (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]]
          ![18600000000 * σ, 11600000000 * σ] 1 = -7000000000 * σ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · show (18600000000 * σ) = _
      simp [Fin.sum_univ_two]
      ring
    · show (11600000000 * σ) = _
      simp [Fin.sum_univ_two]
      ring
  · simp [grayNetPower, Fin.sum_univ_two]
    ring
  · simp [grayNetPower, Fin.sum_univ_two]
    ring

/- Black recovery on the same geometry: with `ε = (1, 1)` the radiosities are
`σ T⁴ = (25600000000 * σ, 8100000000 * σ)` and the net power of the hotter surface is the black
value `17500000000 * σ`. -/
example (σ : ℝ) :
    IsRadiosity σ ![1, 1] ![![0, 1], ![1 / 2, 1 / 2]] ![400, 300]
        ![25600000000 * σ, 8100000000 * σ] ∧
      grayNetPower (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]]
          ![25600000000 * σ, 8100000000 * σ] 0 = 17500000000 * σ := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · show (25600000000 * σ) = _
      simp [Fin.sum_univ_two]
      ring
    · show (8100000000 * σ) = _
      simp [Fin.sum_univ_two]
      ring
  · simp [grayNetPower, Fin.sum_univ_two]
    ring

/- The gray radiosities above are the only solution on this geometry and the gray net powers
balance, through `existsUnique_isRadiosity`, `grayNetPower_eq_emitted_sub_absorbed` and
`sum_grayNetPower_eq_zero`: surface `0` emits `σ 400 ^ 4 / 2` and absorbs half of its
irradiation `11600000000 * σ`. -/
example (σ : ℝ) :
    (∃! J, IsRadiosity σ ![1 / 2, 1 / 2] ![![0, 1], ![1 / 2, 1 / 2]] ![400, 300] J) ∧
      grayNetPower (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]]
          ![18600000000 * σ, 11600000000 * σ] 0 =
        1 * (1 / 2) * (σ * 400 ^ 4 - 11600000000 * σ) ∧
      ∑ i, grayNetPower (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]]
          ![18600000000 * σ, 11600000000 * σ] i = 0 := by
  have hE : IsBlackEnclosure (![1, 2] : Fin 2 → ℝ) ![![0, 1], ![1 / 2, 1 / 2]] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num
    · intro i
      fin_cases i <;> norm_num [Fin.sum_univ_two]
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num
  have hε : ∀ i : Fin 2, 0 < (![1 / 2, 1 / 2] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num
  have hε₁ : ∀ i : Fin 2, (![1 / 2, 1 / 2] : Fin 2 → ℝ) i ≤ 1 := by
    intro i
    fin_cases i <;> norm_num
  have hJ : IsRadiosity σ ![1 / 2, 1 / 2] ![![0, 1], ![1 / 2, 1 / 2]] ![400, 300]
      ![18600000000 * σ, 11600000000 * σ] := by
    intro i
    fin_cases i
    · show (18600000000 * σ) = _
      simp [Fin.sum_univ_two]
      ring
    · show (11600000000 * σ) = _
      simp [Fin.sum_univ_two]
      ring
  refine ⟨existsUnique_isRadiosity hE hε hε₁ σ _, ?_, sum_grayNetPower_eq_zero hE _⟩
  rw [grayNetPower_eq_emitted_sub_absorbed hE hJ 0]
  simp [Fin.sum_univ_two]

end HeatTransfer.EnclosureRadiation
