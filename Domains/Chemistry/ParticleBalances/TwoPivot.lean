/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Two-pivot remapping

Linear interpolation preserves the zeroth and first moments of a single remapping.
The second moment has a factored excess; this describes only the algebraic remapping,
not conservation of particle number under aggregation.
-/

namespace Domains.Chemistry.ParticleBalances.TwoPivot

/-- The two interpolation weights always sum to one and recover the original mass.
Both weights are nonnegative exactly on the closed pivot interval. The second moment
excess is `(m - m₁) * (m₂ - m)`, nonnegative there and positive on its interior.
To the left of the interval the second weight is negative; to the right the first is.

Source: Kumar and Ramkrishna, *Chemical Engineering Science* 51 (1996), 1311–1332,
§§3.2–3.4, for the fixed-pivot construction. -/
public theorem two_pivot_moments (m₁ m₂ m : ℝ) (_hm₁ : 0 < m₁) (hord : m₁ < m₂) :
    let w₁ := (m₂ - m) / (m₂ - m₁)
    let w₂ := (m - m₁) / (m₂ - m₁)
    w₁ + w₂ = 1 ∧ w₁ * m₁ + w₂ * m₂ = m ∧
    ((0 ≤ w₁ ∧ 0 ≤ w₂) ↔ (m₁ ≤ m ∧ m ≤ m₂)) ∧
    w₁ * m₁ ^ 2 + w₂ * m₂ ^ 2 - m ^ 2 = (m - m₁) * (m₂ - m) ∧
    (m₁ ≤ m → m ≤ m₂ → 0 ≤ w₁ * m₁ ^ 2 + w₂ * m₂ ^ 2 - m ^ 2) ∧
    (m₁ < m → m < m₂ → 0 < w₁ * m₁ ^ 2 + w₂ * m₂ ^ 2 - m ^ 2) ∧
    (m < m₁ → w₂ < 0) ∧ (m₂ < m → w₁ < 0) := by
  let w₁ := (m₂ - m) / (m₂ - m₁)
  let w₂ := (m - m₁) / (m₂ - m₁)
  have hd : 0 < m₂ - m₁ := sub_pos.mpr hord
  have hsum : w₁ + w₂ = 1 := by
    dsimp only [w₁, w₂]
    field_simp [hd.ne']
    ring
  have hmass : w₁ * m₁ + w₂ * m₂ = m := by
    dsimp only [w₁, w₂]
    field_simp [hd.ne']
    ring
  have hweights : (0 ≤ w₁ ∧ 0 ≤ w₂) ↔ (m₁ ≤ m ∧ m ≤ m₂) := by
    dsimp only [w₁, w₂]
    simp only [le_div_iff₀ hd, zero_mul, sub_nonneg, and_comm]
  have hsecond : w₁ * m₁ ^ 2 + w₂ * m₂ ^ 2 - m ^ 2 = (m - m₁) * (m₂ - m) := by
    dsimp only [w₁, w₂]
    field_simp [hd.ne']
    ring
  refine ⟨hsum, hmass, hweights, hsecond, ?_, ?_, ?_, ?_⟩
  · intro hl hu
    rw [hsecond]
    exact mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)
  · intro hl hu
    rw [hsecond]
    exact mul_pos (sub_pos.mpr hl) (sub_pos.mpr hu)
  · intro hl
    exact div_neg_of_neg_of_pos (sub_neg.mpr hl) hd
  · intro hu
    exact div_neg_of_neg_of_pos (sub_neg.mpr hu) hd

end Domains.Chemistry.ParticleBalances.TwoPivot
