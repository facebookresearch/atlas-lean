/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Singularity of natural duals of Moebius maps

Fritz Schweiger's remark on singular duals of Moebius maps considers four dual branches, the
Moebius maps
`V^#_{αγ}(y) = (γ - 2α - αy) / (2α + 1 + αy)`,
`V^#_{αδ}(y) = (2αδ - 1 + αδy) / (2α + 1 + αy)`,
`V^#_{βγ}(y) = (2β + γ - 2 + (β + γ - 1)y) / (3 - 2β + (2 - β)y)` and
`V^#_{βδ}(y) = (2δ - 2βδ - 1 + (δ - βδ - 1)y) / (3 - 2β + (2 - β)y)`,
for real parameters with `α > 0`, `β < 1`, `γ > -1` and `δ ≥ 0`. A natural dual `[η, ξ]` has
`η = (-2 + 2β + γ) / (2 - β)`, a fixed point of `V^#_{βγ}`, and its other endpoint `ξ` satisfies
the endpoint equations `V^#_{βγ}(ξ) = V^#_{βδ}(ξ)` and `V^#_{αδ}(ξ) = V^#_{αγ}(ξ)`.

## Main declarations

* `MetaMathlibExt.moebius_dual_endpoint_ne_neg_one`: the two δ-branches disagree at `-1`.
* `MetaMathlibExt.moebius_dual_central_equations`: the endpoint equations at `ξ`, with nonzero
  denominators, force `α + αδ + δ = β + γ + βδ`; if moreover `ξ = V^#_{αγ}(η)`, they force a
  second polynomial relation between `α`, `β`, `γ` and `δ`.
* `MetaMathlibExt.moebius_naturalDual_singular`: when `ξ = V^#_{αγ}(η)`, the two endpoints
  coincide.

## Proof outline

Cleared of their nonzero denominators, the endpoint equations read
`(β + γ - δ + βδ) (2 + ξ) = 1 + γ` and `α (1 + δ) (2 + ξ) = 1 + γ`. As `γ > -1`, the common
right-hand side is nonzero, so `2 + ξ ≠ 0` and the two coefficients agree: this is the first
relation. For the second, multiply `α (1 + δ) (2 + ξ) = 1 + γ` by `2α + 1 + αη` and use
`ξ (2α + 1 + αη) = γ - 2α - αη`, then multiply by `2 - β` and use `η (2 - β) = -2 + 2β + γ`;
`linear_combination` checks that the result is the stated identity.

## Implementation notes

The proof of the central equations uses `β < 1` only through `2 - β ≠ 0` and `γ > -1` only through
`1 + γ ≠ 0`. Its unused hypotheses `hα` and `hδ` retain their names for named arguments.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Moebius dual branches disagree at −1.** Let $\alpha, \beta, \delta$ be real numbers with
$\alpha > 0$, $\beta < 1$ and $\delta \ge 0$, and define the dual branches
$V^\#_{\alpha\delta}(y) = (2\alpha\delta - 1 + \alpha\delta y)/(2\alpha + 1 + \alpha y)$ and
$V^\#_{\beta\delta}(y) = (2\delta - 2\beta\delta - 1 + (\delta - \beta\delta - 1) y)/
(3 - 2\beta + (2 - \beta) y)$. Then $V^\#_{\beta\delta}(-1) \ne V^\#_{\alpha\delta}(-1)$.

Equality would force $\delta = -1$.

Source: Fritz Schweiger, *A Remark on Singular Duals of Moebius Maps*, INTEGERS 24 (2024),
Article A17, Lemma 2 (`integers-2024-A17-lem-2`). -/
theorem moebius_dual_endpoint_ne_neg_one (α β δ : ℝ) (hα : 0 < α) (hβ : β < 1)
    (hδ : 0 ≤ δ) :
    let dualαδ : ℝ → ℝ := fun y => (2 * α * δ - 1 + α * δ * y) / (2 * α + 1 + α * y)
    let dualβδ : ℝ → ℝ := fun y =>
      (2 * δ - 2 * β * δ - 1 + (δ - β * δ - 1) * y) / (3 - 2 * β + (2 - β) * y)
    dualβδ (-1) ≠ dualαδ (-1) := by
  intro dualαδ dualβδ heq
  have hβδ : dualβδ (-1) = δ := by
    apply (div_eq_iff (by linarith only [hβ])).2
    ring
  rw [hβδ] at heq
  have hαden : 2 * α + 1 + α * (-1) ≠ 0 := by linarith only [hα]
  linarith only [(eq_div_iff hαden).mp heq, hδ]

set_option linter.unusedVariables false in
/-- **Central equations for natural duals of Moebius maps.** Let $\alpha, \beta, \gamma, \delta$
and $\xi$ be real numbers with $\alpha > 0$, $\beta < 1$, $\gamma > -1$ and $\delta \ge 0$. Define
the dual branches
$V^\#_{\alpha\gamma}(y) = (\gamma - 2\alpha - \alpha y)/(2\alpha + 1 + \alpha y)$,
$V^\#_{\alpha\delta}(y) = (2\alpha\delta - 1 + \alpha\delta y)/(2\alpha + 1 + \alpha y)$,
$V^\#_{\beta\gamma}(y) = (2\beta + \gamma - 2 + (\beta + \gamma - 1) y)/
(3 - 2\beta + (2 - \beta) y)$ and
$V^\#_{\beta\delta}(y) = (2\delta - 2\beta\delta - 1 + (\delta - \beta\delta - 1) y)/
(3 - 2\beta + (2 - \beta) y)$, and put $\eta = (-2 + 2\beta + \gamma)/(2 - \beta)$. Suppose that
$3 - 2\beta + (2 - \beta)\xi \ne 0$, $2\alpha + 1 + \alpha\xi \ne 0$,
$V^\#_{\beta\gamma}(\xi) = V^\#_{\beta\delta}(\xi)$ and
$V^\#_{\alpha\delta}(\xi) = V^\#_{\alpha\gamma}(\xi)$. Then
$\alpha + \alpha\delta + \delta = \beta + \gamma + \beta\delta$; and if moreover
$2\alpha + 1 + \alpha\eta \ne 0$ and $\xi = V^\#_{\alpha\gamma}(\eta)$, then
$\alpha^2\gamma + \alpha^2\gamma\delta + 2\alpha + \beta + \beta\gamma + 2\alpha^2 +
2\alpha^2\delta + 4\alpha\delta + 2\alpha\gamma\delta = 2 + \alpha\gamma^2 + 2\gamma +
2\alpha\beta + \alpha\gamma + \alpha\beta\gamma + \alpha\beta\gamma\delta + 2\alpha\beta\delta$.

Source: Fritz Schweiger, *A Remark on Singular Duals of Moebius Maps*, INTEGERS 24 (2024),
Article A17, Lemma 3 (`integers-2024-A17-lem-3`). -/
theorem moebius_dual_central_equations (α β γ δ ξ : ℝ) (hα : 0 < α) (hβ : β < 1)
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
                2 * α * β * δ) := by
  intro dualαγ dualαδ dualβγ dualβδ η hβden hαden hβeq hαeq
  -- Cleared of their denominators, both endpoint equations say that a coefficient times `2 + ξ`
  -- equals `1 + γ`.
  have hβδ : (β + γ - δ + β * δ) * (2 + ξ) = 1 + γ := by
    linear_combination (div_left_inj' hβden).mp hβeq
  have hαδ : α * (1 + δ) * (2 + ξ) = 1 + γ := by
    linear_combination (div_left_inj' hαden).mp hαeq
  -- As `1 + γ ≠ 0`, the factor `2 + ξ` is nonzero, so the two coefficients agree.
  have hξ : 2 + ξ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hαδ
    linarith
  refine ⟨by linear_combination mul_right_cancel₀ hξ (hαδ.trans hβδ.symm), fun hηden hξη => ?_⟩
  -- Clear the denominators of `η` and of `ξ = V^#_{αγ}(η)`, and combine with `hαδ`.
  have hη : η * (2 - β) = -2 + 2 * β + γ :=
    div_mul_cancel₀ _ (by linarith : (0 : ℝ) < 2 - β).ne'
  have hξη' : ξ * (2 * α + 1 + α * η) = γ - 2 * α - α * η := by
    rw [hξη]
    exact div_mul_cancel₀ _ hηden
  linear_combination (2 - β) * (2 * α + 1 + α * η) * hαδ - (2 - β) * α * (1 + δ) * hξη' -
    α * (α * (1 + δ) - (1 + γ)) * hη

/-- **Singularity of natural duals of Moebius maps (algebraic form).** Let
$\alpha, \beta, \gamma, \delta$ be real numbers with $\alpha > 0$, $\beta < 1$, $\gamma > -1$ and
$\delta \ge 0$. Define the dual branches
$V^\#_{\alpha\gamma}(y) = (\gamma - 2\alpha - \alpha y)/(2\alpha + 1 + \alpha y)$,
$V^\#_{\alpha\delta}(y) = (2\alpha\delta - 1 + \alpha\delta y)/(2\alpha + 1 + \alpha y)$,
$V^\#_{\beta\gamma}(y) = (2\beta + \gamma - 2 + (\beta + \gamma - 1) y)/
(3 - 2\beta + (2 - \beta) y)$ and
$V^\#_{\beta\delta}(y) = (2\delta - 2\beta\delta - 1 + (\delta - \beta\delta - 1) y)/
(3 - 2\beta + (2 - \beta) y)$, and put $\eta = (-2 + 2\beta + \gamma)/(2 - \beta)$ and
$\xi = V^\#_{\alpha\gamma}(\eta)$. If $2\alpha + 1 + \alpha\eta \ne 0$,
$3 - 2\beta + (2 - \beta)\xi \ne 0$, $2\alpha + 1 + \alpha\xi \ne 0$,
$V^\#_{\beta\gamma}(\xi) = V^\#_{\beta\delta}(\xi)$ and
$V^\#_{\alpha\delta}(\xi) = V^\#_{\alpha\gamma}(\xi)$, then $\xi = \eta$.

Here $\eta$ is a fixed point of $V^\#_{\beta\gamma}$, and $\xi = \eta$ says that the natural dual
$[\eta, \xi]$ reduces to a single point.

Source: Fritz Schweiger, *A Remark on Singular Duals of Moebius Maps*, INTEGERS 24 (2024),
Article A17, Theorem 1 (`integers-2024-A17-thm-1`). -/
theorem moebius_naturalDual_singular (α β γ δ : ℝ) (hα : 0 < α) (hβ : β < 1)
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
      dualβγ ξ = dualβδ ξ → dualαδ ξ = dualαγ ξ → ξ = η := by
  intro dualαγ dualαδ dualβγ dualβδ η ξ hηden hβden hαden hβeq hαeq
  have hcentral := (moebius_dual_central_equations α β γ δ ξ hα hβ hγ hδ
    hβden hαden hβeq hαeq).1
  -- Subtract the first central equation from the cleared α-branch equation and cancel 1 + δ.
  have hαξ : α * (1 + ξ) = 1 - β := by
    apply mul_right_cancel₀ (by linarith : (1 : ℝ) + δ ≠ 0)
    linear_combination (div_left_inj' hαden).mp hαeq - hcentral
  have hξ : ξ * (2 * α + 1 + α * η) = γ - 2 * α - α * η := div_mul_cancel₀ _ hηden
  have hη : η * (2 - β) = -2 + 2 * β + γ := div_mul_cancel₀ _ (by linarith : (2 : ℝ) - β ≠ 0)
  linear_combination hξ - (2 + η) * hαξ - hη

end MetaMathlibExt
