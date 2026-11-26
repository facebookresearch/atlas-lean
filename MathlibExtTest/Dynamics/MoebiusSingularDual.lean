/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.MoebiusSingularDual
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Dynamics.MoebiusSingularDual` -/

namespace MathlibExtTest.Dynamics.MoebiusSingularDual

open MetaMathlibExt

-- At the allowed boundary δ = 0, the two endpoint values are 0 and -1 / (α + 1).
example (α : ℝ) (hα : 0 < α) : (0 : ℝ) ≠ -1 / (α + 1) := by
  simpa [two_mul, add_right_comm] using
    moebius_dual_endpoint_ne_neg_one α 0 0 hα zero_lt_one le_rfl

-- Test section: a singular natural dual. At `α = 1`, `β = 0`, `γ = 2`, `δ = 1/2` the fixed point
-- is `η = (-2 + 2β + γ) / (2 - β) = 0`, and `ξ = V^#_{αγ}(η) = 0` satisfies both endpoint
-- equations with denominators `3` and `3`, so the hypotheses of both parts hold together. The
-- first central equation reads `2 = 2`, the second `12 = 12`.
example : (1 : ℝ) + 1 * (1 / 2) + 1 / 2 = 0 + 2 + 0 * (1 / 2) :=
  (moebius_dual_central_equations 1 0 2 (1 / 2) 0 one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

example :
    (1 : ℝ) ^ 2 * 2 + 1 ^ 2 * 2 * (1 / 2) + 2 * 1 + 0 + 0 * 2 + 2 * 1 ^ 2 + 2 * 1 ^ 2 * (1 / 2) +
        4 * 1 * (1 / 2) + 2 * 1 * 2 * (1 / 2) =
      2 + 1 * 2 ^ 2 + 2 * 2 + 2 * 1 * 0 + 1 * 2 + 1 * 0 * 2 + 1 * 0 * 2 * (1 / 2) +
        2 * 1 * 0 * (1 / 2) :=
  (moebius_dual_central_equations 1 0 2 (1 / 2) 0 one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    (by norm_num) (by norm_num)

-- Test section: the first central equation is an obstruction. When
-- `α + αδ + δ ≠ β + γ + βδ`, a point `ξ` satisfying the first endpoint equation never satisfies
-- the second; the branches are applied with their formulas written out.
example (α β γ δ ξ : ℝ) (hα : 0 < α) (hβ : β < 1) (hγ : -1 < γ) (hδ : 0 ≤ δ)
    (hne : α + α * δ + δ ≠ β + γ + β * δ)
    (hβden : 3 - 2 * β + (2 - β) * ξ ≠ 0) (hαden : 2 * α + 1 + α * ξ ≠ 0)
    (hβeq : (2 * β + γ - 2 + (β + γ - 1) * ξ) / (3 - 2 * β + (2 - β) * ξ) =
      (2 * δ - 2 * β * δ - 1 + (δ - β * δ - 1) * ξ) / (3 - 2 * β + (2 - β) * ξ)) :
    (2 * α * δ - 1 + α * δ * ξ) / (2 * α + 1 + α * ξ) ≠
      (γ - 2 * α - α * ξ) / (2 * α + 1 + α * ξ) := fun hαeq =>
  hne (moebius_dual_central_equations α β γ δ ξ (hα := hα) hβ hγ (hδ := hδ)
    hβden hαden hβeq hαeq).1

-- Test section: the hypothesis `-1 < γ` cannot be dropped. At `γ = -1` the point `ξ = -2`
-- satisfies both endpoint equations, with denominators `-1` and `1`, whatever `α`, `β`, `δ` are;
-- at `α = 1`, `β = 0`, `δ = 0` the first central equation would read `1 = -1`.
example : ¬ ∀ α β γ δ ξ : ℝ, 0 < α → β < 1 → 0 ≤ δ →
    3 - 2 * β + (2 - β) * ξ ≠ 0 → 2 * α + 1 + α * ξ ≠ 0 →
    (2 * β + γ - 2 + (β + γ - 1) * ξ) / (3 - 2 * β + (2 - β) * ξ) =
      (2 * δ - 2 * β * δ - 1 + (δ - β * δ - 1) * ξ) / (3 - 2 * β + (2 - β) * ξ) →
    (2 * α * δ - 1 + α * δ * ξ) / (2 * α + 1 + α * ξ) =
      (γ - 2 * α - α * ξ) / (2 * α + 1 + α * ξ) →
    α + α * δ + δ = β + γ + β * δ := by
  intro h
  have h' := h 1 0 (-1) 0 (-2) one_pos (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at h'

-- At the boundary δ = 0, the dual can collapse to a nonzero endpoint.
example :
    let α : ℝ := 2 / 3
    let β : ℝ := 2 / 3
    let η : ℝ := (-2 + 2 * β + 0) / (2 - β)
    (0 - 2 * α - α * η) / (2 * α + 1 + α * η) = -(1 / 2) := by
  intro α β η
  calc
    _ = η := by
      apply moebius_naturalDual_singular α β 0 0 <;> norm_num [α, β]
    _ = _ := by norm_num [η, β]

end MathlibExtTest.Dynamics.MoebiusSingularDual
