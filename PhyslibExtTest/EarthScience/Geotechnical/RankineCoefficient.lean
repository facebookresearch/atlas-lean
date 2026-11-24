/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.RankineCoefficient
import PhyslibExt.EarthScience.Geotechnical.RankineWall
import PhyslibExt.CondensedMatter.Elasticity.StressStrain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Rankine coefficient checks

Concrete consumers of
`PhyslibExt.EarthScience.Geotechnical.RankineCoefficient`:
the zero-friction and cohesionless focused checks, a strict
nonzero non-vacuity witness, the tensile admission boundary,
the tension-positive sign/order bridge to the Mohr circle with
its negative controls, and the Rankine wall consumer.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Focused checks and non-vacuity
- B. Sign conversion and wall consumer
- C. Domain controls

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.RankineCoefficient`
- `PhyslibExt.EarthScience.Geotechnical.RankineWall`
- `PhyslibExt.CondensedMatter.Elasticity.StressStrain`
-/

open EarthScience

namespace PhyslibExtTest.EarthScience.Geotechnical.RankineCoefficient

/-! ## A. Focused checks and non-vacuity -/

/-- At `φ = 0` the formula is `σ3 = σ1 - 2c`. -/
example (σ1 σ3 c : ℝ) (ho : σ3 ≤ σ1) (h3 : 0 ≤ σ3) (hc : 0 ≤ c) :
    (σ1 - σ3) / 2 = ((σ1 + σ3) / 2) * Real.sin 0 + c * Real.cos 0 ↔
      σ3 = σ1 - 2 * c := by
  rw [rankine_principal_limit_iff ho h3 hc le_rfl (by positivity)]
  simp [rankineActiveCoefficient]

/-- Cohesionless case: `σ3 = K_a σ1`. -/
example (σ1 σ3 φ : ℝ) (ho : σ3 ≤ σ1) (h3 : 0 ≤ σ3) (h0 : 0 ≤ φ)
    (h1 : φ < Real.pi / 2) :
    (σ1 - σ3) / 2 = ((σ1 + σ3) / 2) * Real.sin φ + 0 * Real.cos φ ↔
      σ3 = rankineActiveCoefficient φ * σ1 := by
  rw [rankine_principal_limit_iff ho h3 le_rfl h0 h1]
  simp

/-- Non-vacuity with strict nonzero data (`φ = π/6`,
`c = √3`, `σ1 = 9`, `σ3 = 1`); both sides hold. -/
example : ∃ σ1 σ3 c φ : ℝ, σ3 ≤ σ1 ∧ 0 ≤ σ3 ∧ 0 ≤ c ∧ 0 ≤ φ ∧
    φ < Real.pi / 2 ∧ 0 < c ∧ 0 < φ ∧ 0 < σ3 ∧ σ3 < σ1 ∧
    (σ1 - σ3) / 2 = ((σ1 + σ3) / 2) * Real.sin φ + c * Real.cos φ ∧
    σ3 = rankineActiveCoefficient φ * σ1
      - 2 * c * Real.sqrt (rankineActiveCoefficient φ) := by
  have h0 : (0 : ℝ) ≤ Real.pi / 6 := by positivity
  have h1 : Real.pi / 6 < Real.pi / 2 := by linarith [Real.pi_pos]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine ⟨9, 1, Real.sqrt 3, Real.pi / 6, by norm_num, by norm_num,
    Real.sqrt_nonneg _, h0, h1, by positivity, by positivity, by norm_num,
    by norm_num, ?_, ?_⟩
  · rw [Real.sin_pi_div_six, Real.cos_pi_div_six]
    linear_combination (-1 / 2 : ℝ) * h3
  · rw [sqrt_rankineActiveCoefficient h0 h1]
    unfold rankineActiveCoefficient
    rw [Real.sin_pi_div_six, Real.cos_pi_div_six]
    linear_combination (2 / 3 : ℝ) * h3

/-- Discrimination: the same data with `σ3 = 2` misses the
limit. -/
example : ¬ ((9 - 2) / 2
    = ((9 + 2) / 2) * Real.sin (Real.pi / 6)
      + Real.sqrt 3 * Real.cos (Real.pi / 6)) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [Real.sin_pi_div_six, Real.cos_pi_div_six]
  intro h
  nlinarith [h3]

/-- Tensile `σ3` is outside admission: the algebra holds at
`σ1 = c = 10`, `φ = 0`, `σ3 = -10`, but `0 ≤ σ3` fails, so
the theorem does not apply there. -/
example : ((10 : ℝ) - (-10)) / 2
      = ((10 + (-10)) / 2) * Real.sin 0 + 10 * Real.cos 0 ∧
    (-10 : ℝ) = rankineActiveCoefficient 0 * 10
      - 2 * 10 * Real.sqrt (rankineActiveCoefficient 0) ∧
    ¬ (0 : ℝ) ≤ -10 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  simp [rankineActiveCoefficient]
  norm_num

/-! ## B. Sign conversion and wall consumer -/

/-- Tension-positive principal values `s₁ ≥ s₃` convert by
negate-and-swap, `σ1 = -s₃`, `σ3 = -s₁`: the Mohr radius is
kept, the center negated, and the order preserved. -/
example (s₁ s₃ : ℝ) (hle : s₃ ≤ s₁) :
    ((-s₃) - (-s₁)) / 2
      = |Elasticity.principalPlaneShear s₁ s₃ (Real.pi / 4)| ∧
    ((-s₃) + (-s₁)) / 2 = -Elasticity.mohrMean s₁ s₃ ∧ (-s₁ ≤ -s₃) := by
  refine ⟨?_, by unfold Elasticity.mohrMean; ring, by linarith⟩
  rw [Elasticity.principalPlaneShear_max s₁ s₃ hle]
  ring

/-- Negative controls: unconverted or unswapped
tension-positive inputs miss the limit at `φ = π/6`, `c = 0`. -/
example : ((3 : ℝ) - 1) / 2
      = ((3 + 1) / 2) * Real.sin (Real.pi / 6) + 0 * Real.cos (Real.pi / 6) ∧
    ¬ (((-1 : ℝ) - (-3)) / 2
      = ((-1 + -3) / 2) * Real.sin (Real.pi / 6)
        + 0 * Real.cos (Real.pi / 6)) ∧
    ¬ (((1 : ℝ) - 3) / 2
      = ((1 + 3) / 2) * Real.sin (Real.pi / 6)
        + 0 * Real.cos (Real.pi / 6)) ∧
    ¬ ((3 : ℝ) ≤ 1) := by
  rw [Real.sin_pi_div_six]
  norm_num

/-- Range on the domain: `0 < K_a ≤ 1`. -/
example {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < Real.pi / 2) :
    0 < rankineActiveCoefficient φ ∧ rankineActiveCoefficient φ ≤ 1 :=
  rankineActiveCoefficient_pos_le_one h0 h1

/-- Wall consumer: with `c = 0` and `σ1 = γ z`, the limit
states `σ3 = rankineActivePressure K_a γ z`. -/
example {γ z φ : ℝ} (hγz : 0 ≤ γ * z) (h0 : 0 ≤ φ)
    (h1 : φ < Real.pi / 2) :
    (γ * z - rankineActivePressure (rankineActiveCoefficient φ) γ z) / 2
      = ((γ * z
          + rankineActivePressure (rankineActiveCoefficient φ) γ z) / 2)
          * Real.sin φ + 0 * Real.cos φ := by
  have hK1 : rankineActiveCoefficient φ ≤ 1 :=
    (rankineActiveCoefficient_pos_le_one h0 h1).2
  have hK0 : 0 ≤ rankineActiveCoefficient φ :=
    (rankineActiveCoefficient_pos_le_one h0 h1).1.le
  have hp : rankineActivePressure (rankineActiveCoefficient φ) γ z
      = rankineActiveCoefficient φ * (γ * z) := by
    unfold rankineActivePressure
    ring
  rw [rankine_principal_limit_iff (by rw [hp]; nlinarith)
    (by rw [hp]; exact mul_nonneg hK0 hγz) le_rfl h0 h1, hp]
  ring

/-- The coefficient's positivity feeds the wall resultant
height `H / 3`. -/
example {γ H φ : ℝ} (hγ : 0 < γ) (hH : 0 < H) (h0 : 0 ≤ φ)
    (h1 : φ < Real.pi / 2) :
    H - PhyslibExt.Mechanics.LinearPressurePanel.linearPressureMoment
          (rankineActiveCoefficient φ * γ) 1 0 H
        / PhyslibExt.Mechanics.LinearPressurePanel.linearPressureForce
          (rankineActiveCoefficient φ * γ) 1 0 H = H / 3 := by
  have hK0 : 0 < rankineActiveCoefficient φ :=
    (rankineActiveCoefficient_pos_le_one h0 h1).1
  exact rankine_resultant_height hK0 hγ hH

/-! ## C. Domain controls -/

/-- The strict bound `φ < π/2` is necessary: beyond it, at
`φ = 5π/6` with all admission premises satisfied, the limit
holds and the formula fails. -/
example : ∃ σ1 σ3 c φ : ℝ, σ3 ≤ σ1 ∧ 0 ≤ σ3 ∧ 0 ≤ c ∧ 0 ≤ φ ∧
    ¬ φ < Real.pi / 2 ∧
    (σ1 - σ3) / 2 = ((σ1 + σ3) / 2) * Real.sin φ + c * Real.cos φ ∧
    ¬ σ3 = rankineActiveCoefficient φ * σ1
      - 2 * c * Real.sqrt (rankineActiveCoefficient φ) := by
  have hs : Real.sin (5 * Real.pi / 6) = 1 / 2 := by
    rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_six]
  have hc : Real.cos (5 * Real.pi / 6) = -(Real.sqrt 3 / 2) := by
    rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_six]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h31 : Real.sqrt 3 * Real.sqrt (1 / 3) = 1 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  refine ⟨6, 4, Real.sqrt 3, 5 * Real.pi / 6, by norm_num, by norm_num,
    Real.sqrt_nonneg _, by positivity, by linarith [Real.pi_pos], ?_, ?_⟩
  · rw [hs, hc]
    linear_combination (1 / 2 : ℝ) * h3
  · unfold rankineActiveCoefficient
    rw [hs, show ((1 : ℝ) - 1 / 2) / (1 + 1 / 2) = 1 / 3 by norm_num]
    intro h
    nlinarith [h31]

/-- Wrong-sign cohesion term (`+ 2 c √K_a`) disagrees at
`φ = 0`, `c = 1`, `σ1 = 3`, `σ3 = 1`. -/
example : ((3 : ℝ) - 1) / 2
      = ((3 + 1) / 2) * Real.sin 0 + 1 * Real.cos 0 ∧
    (1 : ℝ) ≠ rankineActiveCoefficient 0 * 3
      + 2 * 1 * Real.sqrt (rankineActiveCoefficient 0) := by
  simp [rankineActiveCoefficient]
  norm_num

#print axioms EarthScience.rankineActiveCoefficient_pos_le_one
#print axioms EarthScience.sqrt_rankineActiveCoefficient
#print axioms EarthScience.sqrt_rankineActiveCoefficient'
#print axioms EarthScience.rankine_principal_limit_iff

end PhyslibExtTest.EarthScience.Geotechnical.RankineCoefficient
