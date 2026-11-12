/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
/-!
# Mass and mole fractions convert correctly

With mole fractions `x` summing to `1` and total mass per mole
`D = ∑ j, x j * M j > 0`, the mass fractions `w i = x i * M i / D`
sum to `1`. Conversely, with mass fractions `w` summing to `1`,
positive molar masses `M`, and `D = ∑ j, w j / M j > 0`, the mole
fractions `(w i / M i) / D` sum to `1` and recover `w`.

## i. Overview

Both directions are field arithmetic over finite sums: the common
denominator factors out of the sum, and the recovery direction cancels
each molar mass. No claim is made about activity, non-ideality, or
species with zero molar mass (excluded by `0 < M i` / `0 < D`).

## ii. Key results

- `EarthScience.mass_fractions_sum`: mass fractions from mole fractions
  sum to `1`.
- `EarthScience.mole_fractions_sum_and_recovery`: mole fractions from
  mass fractions sum to `1` and recover the mass fractions.

## iii. References

- `Finset.sum_div`, `div_self`, `div_mul_cancel₀` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Mass fractions from mole fractions: with mole fractions `x` summing to `1`,
positive molar masses `M`, and total mass per mole `D = ∑ j, x j * M j > 0`,
the mass fractions `w i = x i * M i / D` sum to `1`. -/
theorem mass_fractions_sum {n : ℕ} (x M : Fin n → ℝ)
    (hx : ∑ i, x i = 1)
    (hD : 0 < ∑ j, x j * M j) :
    ∑ i, (x i * M i) / (∑ j, x j * M j) = 1 := by
  have _ := hx
  have hDne : (∑ j, x j * M j) ≠ 0 := ne_of_gt hD
  rw [← Finset.sum_div]
  exact div_self hDne

/-- Mole fractions from mass fractions, with recovery: with mass fractions `w`
summing to `1`, positive molar masses `M`, and `D = ∑ j, w j / M j > 0`,
the mole fractions `x i = (w i / M i) / D` sum to `1` and recover `w`,
i.e. `(x i * M i) / (∑ j, x j * M j) = w i` for every `i`. -/
theorem mole_fractions_sum_and_recovery {n : ℕ} (w M : Fin n → ℝ)
    (hw : ∑ i, w i = 1) (hM : ∀ i, 0 < M i)
    (hD : 0 < ∑ j, w j / M j) :
    (∑ i, (w i / M i) / (∑ j, w j / M j) = 1) ∧
      (∀ i, ((w i / M i) / (∑ j, w j / M j) * M i) /
        (∑ j, ((w j / M j) / (∑ k, w k / M k)) * M j) = w i) := by
  have hDne : (∑ j, w j / M j) ≠ 0 := ne_of_gt hD
  have hMne : ∀ i, M i ≠ 0 := fun i => ne_of_gt (hM i)
  refine ⟨?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self hDne
  · intro i
    have hnum : ((w i / M i) / (∑ j, w j / M j) * M i) = (w i / (∑ j, w j / M j)) := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (hMne i)]
    have hterm : ∀ j, (((w j / M j) / (∑ k, w k / M k)) * M j) = (w j / (∑ k, w k / M k)) := by
      intro j
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (hMne j)]
    have hden : (∑ j, (((w j / M j) / (∑ k, w k / M k)) * M j)) = (1 / (∑ k, w k / M k)) := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      rw [← Finset.sum_div, hw]
    rw [hnum, hden]
    field_simp

end EarthScience
