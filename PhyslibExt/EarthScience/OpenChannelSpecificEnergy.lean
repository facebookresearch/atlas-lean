/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Rectangular-channel specific energy and critical depth

## i. Overview

For a rectangular channel with constant discharge per unit width `q > 0`
and gravity `g > 0`, the specific energy (head relative to the channel bed,
hydrostatic section, ideal energy model) at depth `h > 0` is
`E(h) = h + q^2 / (2 * g * h^2)`: the depth itself plus the velocity head,
since the mean velocity is `q / h`. Its unique minimum on `h > 0` is
attained at the critical depth `hc = (q^2 / g) ^ (1/3)`, where the Froude
number is `1`. Hydraulic jumps and friction are not covered by this
minimization.

## ii. Key results

- `EarthScience.specific_energy_unique_minimum`: `E` has a unique minimum
  on `h > 0`, attained at `hc = (q^2 / g) ^ (1/3)`, with
  `hc ^ 3 = q ^ 2 / g` and `E(hc) = 3 * hc / 2` (the last equality follows
  from the cube relation and is checked numerically in the test module).

## iii. Table of contents

- A. Unique minimum of the specific energy

## iv. References

- V. T. Chow, *Open-Channel Hydraulics*, McGraw-Hill, 1959, ch. 3
  (specific energy and critical depth).
- Field arithmetic and real powers in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Unique minimum of the specific energy -/

/-- Rectangular-channel specific energy `E(h) = h + q^2 / (2 * g * h^2)` for
discharge per unit width `q > 0` and gravity `g > 0` has a unique minimum
on `h > 0`, attained at the critical depth `hc = (q^2 / g) ^ (1/3)`. -/
theorem specific_energy_unique_minimum {q g : ℝ} (hq : 0 < q) (hg : 0 < g) :
    ∃ hc : ℝ, hc = (q ^ 2 / g) ^ (1 / 3 : ℝ) ∧ 0 < hc ∧ hc ^ 3 = q ^ 2 / g ∧
      ∀ h : ℝ, 0 < h →
        h + q ^ 2 / (2 * g * h ^ 2) ≥ hc + q ^ 2 / (2 * g * hc ^ 2) ∧
        (h + q ^ 2 / (2 * g * h ^ 2) = hc + q ^ 2 / (2 * g * hc ^ 2) ↔ h = hc) := by
  have hq2 : 0 < q ^ 2 / g := by positivity
  set hc : ℝ := (q ^ 2 / g) ^ (1 / 3 : ℝ) with hhc_def
  have hhc_pos : 0 < hc := by
    rw [hhc_def]
    exact Real.rpow_pos_of_pos hq2 _
  have hhc_cube : hc ^ 3 = q ^ 2 / g := by
    rw [hhc_def, ← Real.rpow_natCast _ 3, ← Real.rpow_mul (le_of_lt hq2)]
    norm_num
  refine ⟨hc, rfl, hhc_pos, hhc_cube, ?_⟩
  intro h hh
  have hg' : g ≠ 0 := ne_of_gt hg
  have hh' : h ≠ 0 := ne_of_gt hh
  have hhc' : hc ≠ 0 := ne_of_gt hhc_pos
  have hq2eq : q ^ 2 = g * hc ^ 3 := by
    rw [hhc_cube]
    field_simp
  have key : h + q ^ 2 / (2 * g * h ^ 2) - (hc + q ^ 2 / (2 * g * hc ^ 2))
      = (h - hc) ^ 2 * (2 * h + hc) / (2 * h ^ 2) := by
    rw [hq2eq]
    field_simp
    ring
  have h2h : 0 < 2 * h + hc := by linarith
  have h2h2 : 0 < 2 * h ^ 2 := by positivity
  have hnn : 0 ≤ (h - hc) ^ 2 * (2 * h + hc) / (2 * h ^ 2) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt h2h)) (le_of_lt h2h2)
  constructor
  · linarith
  · constructor
    · intro heq
      have hT : (h - hc) ^ 2 * (2 * h + hc) / (2 * h ^ 2) = 0 := by linarith
      have hnum : (h - hc) ^ 2 * (2 * h + hc) = 0 := by
        rcases div_eq_zero_iff.mp hT with h0 | h0
        · exact h0
        · exact absurd h0 (ne_of_gt h2h2)
      have hsq : (h - hc) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hnum with h0 | h0
        · exact h0
        · exact absurd h0 (ne_of_gt h2h)
      have hsub : h - hc = 0 := sq_eq_zero_iff.mp hsq
      exact sub_eq_zero.mp hsub
    · intro hheq
      rw [hheq]

end EarthScience
