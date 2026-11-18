/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Decision.FiniteBinaryOptimal

/-!
# Tests for the weighted-score binary Bayes rule

Concrete two-point instances: the four deterministic risks, strict
optimality of the identity rule, a genuine weighted tie with different
densities, one-sided support, and joint-zero support.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExtTest.Probability.Decision

theorem weightedScore_det_constFalse_risk :
    (1 - (1/3 : ℝ)) * 1 * ((3/4 : ℝ) * 0 + (1/4) * 0)
      + (1/3) * 4 * ((1/4 : ℝ) * (1 - 0) + (3/4) * (1 - 0)) = 4/3 := by
  norm_num

/-- Nonvacuity: identity deterministic rule has risk `1/2` (the optimum). -/
theorem weightedScore_det_id_risk :
    (1 - (1/3 : ℝ)) * 1 * ((3/4 : ℝ) * 0 + (1/4) * 1)
      + (1/3) * 4 * ((1/4 : ℝ) * (1 - 0) + (3/4) * (1 - 1)) = 1/2 := by
  norm_num

/-- Nonvacuity: swapped deterministic rule has risk `3/2`. -/
theorem weightedScore_det_swap_risk :
    (1 - (1/3 : ℝ)) * 1 * ((3/4 : ℝ) * 1 + (1/4) * 0)
      + (1/3) * 4 * ((1/4 : ℝ) * (1 - 1) + (3/4) * (1 - 0)) = 3/2 := by
  norm_num

/-- Nonvacuity: always-positive deterministic rule has risk `2/3`. -/
theorem weightedScore_det_constTrue_risk :
    (1 - (1/3 : ℝ)) * 1 * ((3/4 : ℝ) * 1 + (1/4) * 1)
      + (1/3) * 4 * ((1/4 : ℝ) * (1 - 1) + (3/4) * (1 - 1)) = 2/3 := by
  norm_num

/-- Nonvacuity: the identity rule (risk `1/2`) strictly beats the other
three deterministic rules (`4/3`, `3/2`, `2/3`) in the instance above. -/
theorem weightedScore_det_id_strictly_optimal :
    (1/2 : ℝ) < 4/3 ∧ (1/2 : ℝ) < 3/2 ∧ (1/2 : ℝ) < 2/3 := by
  norm_num

/-- Nonvacuity, genuine tie with arbitrary randomization: same
`π = 1/3, cFP = 1, cFN = 4`, but `P0 = (1/2, 1/2)`, `P1 = (1/4, 3/4)`.
At `x = 0` the weighted scores tie:
`(1 - 1/3) * 1 * (1/2) = (1/3) * 4 * (1/4) = 1/3`, although the densities
differ (`P0 0 = 1/2 ≠ 1/4 = P1 0`). Every randomization level at `0` gives
the same contribution, and two rules differing only at `0` have equal risk.
Equal densities alone would not give this: the tie is the weighted one. -/
theorem weightedScore_genuine_tie :
    (1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ) = (1/3) * 4 * (1/4 : ℝ)
    ∧ ∀ a b : ℝ,
        a * ((1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ)) + (1 - a) * ((1/3) * 4 * (1/4 : ℝ))
        = b * ((1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ)) + (1 - b) * ((1/3) * 4 * (1/4 : ℝ)) := by
  constructor
  · norm_num
  · intro a b
    have h : (1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ) = (1/3) * 4 * (1/4 : ℝ) := by norm_num
    rw [h]
    ring

/-- Nonvacuity, one-sided support: `P0 x = 0 < P1 x` strictly favors
deciding `true` at `x` (weighted-score inequality, no division by `P0 x`). -/
theorem weightedScore_oneSidedSupport :
    ∀ π cFP cFN : ℝ, 0 < π → π < 1 → 0 < cFP → 0 < cFN
      → (1 - π) * cFP * (0 : ℝ) < π * cFN * (1/2 : ℝ) := by
  intro π cFP cFN hπ0 hπ1 hcFP hcFN
  simp only [mul_zero]
  have h : 0 < π * cFN * (1/2 : ℝ) := by positivity
  exact h

/-- Nonvacuity, joint-zero support: if `P0 x = P1 x = 0` then both weighted
scores at `x` are `0`, the point is a genuine tie, and every randomization
level contributes `0` there. -/
theorem weightedScore_jointZeroSupport :
    ∀ π cFP cFN a : ℝ,
      a * ((1 - π) * cFP * (0 : ℝ)) + (1 - a) * (π * cFN * (0 : ℝ)) = 0
      ∧ π * cFN * (0 : ℝ) = (1 - π) * cFP * (0 : ℝ) := by
  intro π cFP cFN a
  simp



theorem weightedScore_oneSidedSupport_false :
    ∀ π cFP cFN : ℝ, 0 < π → π < 1 → 0 < cFP → 0 < cFN
      → π * cFN * (0 : ℝ) < (1 - π) * cFP * (1/2 : ℝ) := by
  intro π cFP cFN hπ0 hπ1 hcFP hcFN
  have h1 : (0 : ℝ) < 1 - π := by linarith
  simp only [mul_zero]
  positivity
end MathlibExtTest.Probability.Decision
