/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

@[expose] public section

/-!
# The linear Cournot duopoly equilibrium

Two firms choose outputs `q₁, q₂ ≥ 0`; the inverse demand is linear, `P(Q) = a - b Q` for total
output `Q` (not truncated at zero), and marginal costs are constant, `c₁` and `c₂`. With `b > 0`
and costs such that both candidate outputs are nonnegative, the outputs
`q₁ = (a - 2 c₁ + c₂) / (3 b)` and `q₂ = (a - 2 c₂ + c₁) / (3 b)` form a Cournot–Nash equilibrium:
each maximizes the firm's concave quadratic profit over nonnegative outputs given the rival's.

## Main results

* `isCournotNash_linear`: the linear Cournot candidate is a Cournot–Nash equilibrium.

## References

* A. A. Cournot, *Recherches sur les principes mathématiques de la théorie des richesses*,
  Hachette (1838), Chapter VII.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), Section 12.C (the Cournot model).
-/

namespace MathlibExt.Economics.Cournot

/-- Profit of a firm producing `q` while its rival produces `r`, under the linear inverse demand
`P(Q) = a - b Q` for total output `Q = q + r` and constant marginal cost `c`:
`q (a - b (q + r)) - c q`. -/
def profit (a b c q r : ℝ) : ℝ :=
  q * (a - b * (q + r)) - c * q

/-- A Cournot–Nash equilibrium `(q₁, q₂)` of the duopoly with demand `a - b Q` and marginal costs
`c₁, c₂`: both outputs are nonnegative and no firm gains by switching to another nonnegative
output, the rival's output held fixed. -/
def IsCournotNash (a b c₁ c₂ q₁ q₂ : ℝ) : Prop :=
  0 ≤ q₁ ∧ 0 ≤ q₂ ∧ (∀ q, 0 ≤ q → profit a b c₁ q q₂ ≤ profit a b c₁ q₁ q₂) ∧
    ∀ q, 0 ≤ q → profit a b c₂ q q₁ ≤ profit a b c₂ q₂ q₁

/-- **Linear Cournot equilibrium.** With `b > 0` and costs such that both candidate outputs are
nonnegative (`a - 2 c₁ + c₂ ≥ 0` and `a - 2 c₂ + c₁ ≥ 0`), the outputs
`q₁ = (a - 2 c₁ + c₂) / (3 b)` and `q₂ = (a - 2 c₂ + c₁) / (3 b)` form a Cournot–Nash
equilibrium. -/
theorem isCournotNash_linear {a b c₁ c₂ : ℝ} (hb : 0 < b) (h₁ : 0 ≤ a - 2 * c₁ + c₂)
    (h₂ : 0 ≤ a - 2 * c₂ + c₁) :
    IsCournotNash a b c₁ c₂ ((a - 2 * c₁ + c₂) / (3 * b)) ((a - 2 * c₂ + c₁) / (3 * b)) := by
  have hb' : b ≠ 0 := ne_of_gt hb
  have h3b : 0 < 3 * b := by positivity
  have h3b' : 3 * b ≠ 0 := ne_of_gt h3b
  set q₁ : ℝ := (a - 2 * c₁ + c₂) / (3 * b) with hq₁
  set q₂ : ℝ := (a - 2 * c₂ + c₁) / (3 * b) with hq₂
  have hFOC₁ : a - 2 * b * q₁ - b * q₂ - c₁ = 0 := by
    rw [hq₁, hq₂]
    field_simp
    ring
  have hFOC₂ : a - 2 * b * q₂ - b * q₁ - c₂ = 0 := by
    rw [hq₁, hq₂]
    field_simp
    ring
  have hdiff₁ : ∀ q : ℝ, profit a b c₁ q₁ q₂ - profit a b c₁ q q₂ = b * (q - q₁) ^ 2 := by
    intro q
    have hlin : profit a b c₁ q₁ q₂ - profit a b c₁ q q₂ - b * (q - q₁) ^ 2
        = (q₁ - q) * (a - 2 * b * q₁ - b * q₂ - c₁) := by
      unfold profit
      ring
    rw [hFOC₁, mul_zero] at hlin
    linarith
  have hdiff₂ : ∀ q : ℝ, profit a b c₂ q₂ q₁ - profit a b c₂ q q₁ = b * (q - q₂) ^ 2 := by
    intro q
    have hlin : profit a b c₂ q₂ q₁ - profit a b c₂ q q₁ - b * (q - q₂) ^ 2
        = (q₂ - q) * (a - 2 * b * q₂ - b * q₁ - c₂) := by
      unfold profit
      ring
    rw [hFOC₂, mul_zero] at hlin
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq₁]
    exact div_nonneg h₁ (le_of_lt h3b)
  · rw [hq₂]
    exact div_nonneg h₂ (le_of_lt h3b)
  · intro q _
    have hnn : 0 ≤ b * (q - q₁) ^ 2 := mul_nonneg (le_of_lt hb) (sq_nonneg _)
    have h := hdiff₁ q
    linarith
  · intro q _
    have hnn : 0 ≤ b * (q - q₂) ^ 2 := mul_nonneg (le_of_lt hb) (sq_nonneg _)
    have h := hdiff₂ q
    linarith

end MathlibExt.Economics.Cournot
