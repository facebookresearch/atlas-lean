/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic

/-! # Singular duals of Moebius maps

Statement-only request from Schweiger's remark on singular duals of Moebius maps.

Conventions (journal PDF, Section 1). The composed map `S ∘ T` has the four inverse branches with
matrices `V_{αγ}, V_{αδ}, V_{βγ}, V_{βδ}` printed in the source, for parameters `0 < α ≤ 1`,
`β < 1`, `-1 < γ`, `0 ≤ δ`; a matrix `(a₀₀ a₀₁; a₁₀ a₁₁)` has dual branch
`V^# y = (a₀₁ + a₁₁ y) / (a₀₀ + a₁₀ y)`. A natural dual `B^# = [η, ξ]` has `η` the fixed point of
`V^#_{βγ}`, `ξ = V^#_{αγ} η`, and satisfies `V^#_{βγ} ξ = V^#_{βδ} ξ`, `V^#_{αδ} ξ = V^#_{αγ} ξ`,
`V^#_{βδ} η = V^#_{αδ} η`; it is singular when `B^#` is one point, `ξ = η`. The dual branches
below are written out from the printed product matrices (which use `V_δ = (2 δ-1; 1 δ)`, while
`V_δ` itself is printed as `(2 δ-1; 1 -δ)`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The fixed-point equation `(-2 + 2β + γ + (-1 + β + γ) η) / (3 - 2β + (2 - β) η) = η` has exactly
the solutions `η = -1` and `η = (-2 + 2β + γ) / (2 - β)`: for real `β ≠ 2` and `γ`, and every real
`η` at which the denominator is nonzero, the equation holds if and only if `η` is one of these two
values. The hypotheses `β ≠ 2` (so that the second value is defined) and the nonzero denominator
make the equation meaningful; the paper's further side conditions on `β, γ` are not used.

Source: Fritz Schweiger, *A Remark on Singular Duals of Moebius Maps*, INTEGERS 24 (2024),
Article A17, Lemma 1 (`integers-2024-A17-lem-1`). -/
public theorem_wanted moebius_fixedPoint_eq_iff (β γ η : ℝ) (hβ : β ≠ 2)
    (hden : 3 - 2 * β + (2 - β) * η ≠ 0) :
    (-2 + 2 * β + γ + (-1 + β + γ) * η) / (3 - 2 * β + (2 - β) * η) = η ↔
      η = -1 ∨ η = (-2 + 2 * β + γ) / (2 - β)

/-- Lemma 2: the endpoint `η = -1` is impossible: for `α > 0`, `β < 1`, `δ ≥ 0`,
`V^#_{βδ}(-1) ≠ V^#_{αδ}(-1)` (the equation would force `δ = -1`).

Source: Fritz Schweiger, *A Remark on Singular Duals of Moebius Maps*, INTEGERS 24 (2024),
Article A17, Lemma 2 (`integers-2024-A17-lem-2`). -/
public theorem_wanted moebius_dual_endpoint_ne_neg_one (α β δ : ℝ) (hα : 0 < α) (hβ : β < 1)
    (hδ : 0 ≤ δ) :
    let dualαδ : ℝ → ℝ := fun y => (2 * α * δ - 1 + α * δ * y) / (2 * α + 1 + α * y)
    let dualβδ : ℝ → ℝ := fun y =>
      (2 * δ - 2 * β * δ - 1 + (δ - β * δ - 1) * y) / (3 - 2 * β + (2 - β) * y)
    dualβδ (-1) ≠ dualαδ (-1)

/-- Lemma 3 (the central equations): if `ξ` satisfies `V^#_{βγ} ξ = V^#_{βδ} ξ` and
`V^#_{αδ} ξ = V^#_{αγ} ξ` (denominators nonzero), with `α > 0`, `β < 1`, `γ > -1`, `δ ≥ 0`, then
`α + αδ + δ = β + γ + βδ`; if moreover `ξ = V^#_{αγ} η` for `η = (-2 + 2β + γ)/(2 - β)`, then
`α²γ + α²γδ + 2α + β + βγ + 2α² + 2α²δ + 4αδ + 2αγδ = 2 + αγ² + 2γ + 2αβ + αγ + αβγ + αβγδ + 2αβδ`.

Source: Fritz Schweiger, *A Remark on Singular Duals of Moebius Maps*, INTEGERS 24 (2024),
Article A17, Lemma 3 (`integers-2024-A17-lem-3`). -/
public theorem_wanted moebius_dual_central_equations (α β γ δ ξ : ℝ) (hα : 0 < α) (hβ : β < 1)
    (hγ : -1 < γ) (hδ : 0 ≤ δ) :
    let dualαγ : ℝ → ℝ := fun y => (γ - 2 * α - α * y) / (2 * α + 1 + α * y)
    let dualαδ : ℝ → ℝ := fun y => (2 * α * δ - 1 + α * δ * y) / (2 * α + 1 + α * y)
    let dualβγ : ℝ → ℝ := fun y =>
      (2 * β + γ - 2 + (β + γ - 1) * y) / (3 - 2 * β + (2 - β) * y)
    let dualβδ : ℝ → ℝ := fun y =>
      (2 * δ - 2 * β * δ - 1 + (δ - β * δ - 1) * y) / (3 - 2 * β + (2 - β) * y)
    let η : ℝ := (-2 + 2 * β + γ) / (2 - β)
    3 - 2 * β + (2 - β) * ξ ≠ 0 → 2 * α + 1 + α * ξ ≠ 0 →
      dualβγ ξ = dualβδ ξ → dualαδ ξ = dualαγ ξ →
        α + α * δ + δ = β + γ + β * δ ∧
          (2 * α + 1 + α * η ≠ 0 → ξ = dualαγ η →
            α ^ 2 * γ + α ^ 2 * γ * δ + 2 * α + β + β * γ + 2 * α ^ 2 + 2 * α ^ 2 * δ +
                4 * α * δ + 2 * α * γ * δ =
              2 + α * γ ^ 2 + 2 * γ + 2 * α * β + α * γ + α * β * γ + α * β * γ * δ +
                2 * α * β * δ)

/-- Theorem 1 (algebraic form): a natural dual of `S ∘ T` is singular. With `η` the fixed point
`(-2 + 2β + γ)/(2 - β)` of `V^#_{βγ}` (Lemmas 1 and 2) and `ξ = V^#_{αγ} η`, the endpoint
equations `V^#_{βγ} ξ = V^#_{βδ} ξ` and `V^#_{αδ} ξ = V^#_{αγ} ξ` (denominators nonzero) force
`ξ = η`, i.e. `B^#` is a single point.

Source: Fritz Schweiger, *A Remark on Singular Duals of Moebius Maps*, INTEGERS 24 (2024),
Article A17, Theorem 1 (`integers-2024-A17-thm-1`). -/
public theorem_wanted moebius_naturalDual_singular (α β γ δ : ℝ) (hα : 0 < α) (hβ : β < 1)
    (hγ : -1 < γ) (hδ : 0 ≤ δ) :
    let dualαγ : ℝ → ℝ := fun y => (γ - 2 * α - α * y) / (2 * α + 1 + α * y)
    let dualαδ : ℝ → ℝ := fun y => (2 * α * δ - 1 + α * δ * y) / (2 * α + 1 + α * y)
    let dualβγ : ℝ → ℝ := fun y =>
      (2 * β + γ - 2 + (β + γ - 1) * y) / (3 - 2 * β + (2 - β) * y)
    let dualβδ : ℝ → ℝ := fun y =>
      (2 * δ - 2 * β * δ - 1 + (δ - β * δ - 1) * y) / (3 - 2 * β + (2 - β) * y)
    let η : ℝ := (-2 + 2 * β + γ) / (2 - β)
    let ξ : ℝ := dualαγ η
    2 * α + 1 + α * η ≠ 0 → 3 - 2 * β + (2 - β) * ξ ≠ 0 → 2 * α + 1 + α * ξ ≠ 0 →
      dualβγ ξ = dualβδ ξ → dualαδ ξ = dualαγ ξ → ξ = η

end

end MetaMathlibExt
