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

/-- **Fixed points of a Moebius dual branch.** Let $\beta, \gamma, \eta$ be real numbers with
$\beta \ne 2$ and $3 - 2\beta + (2 - \beta)\eta \ne 0$. Then
$(-2 + 2\beta + \gamma + (-1 + \beta + \gamma)\eta)/(3 - 2\beta + (2 - \beta)\eta) = \eta$
if and only if $\eta = -1$ or $\eta = (-2 + 2\beta + \gamma)/(2 - \beta)$.

The paper's further side conditions on $\beta$ and $\gamma$ are not used.

Source: Fritz Schweiger, *A Remark on Singular Duals of Moebius Maps*, INTEGERS 24 (2024),
Article A17, Lemma 1 (`integers-2024-A17-lem-1`). -/
public theorem_wanted moebius_fixedPoint_eq_iff (β γ η : ℝ) (hβ : β ≠ 2)
    (hden : 3 - 2 * β + (2 - β) * η ≠ 0) :
    (-2 + 2 * β + γ + (-1 + β + γ) * η) / (3 - 2 * β + (2 - β) * η) = η ↔
      η = -1 ∨ η = (-2 + 2 * β + γ) / (2 - β)

/-- **Moebius dual branches disagree at −1.** Let $\alpha, \beta, \delta$ be real numbers with
$\alpha > 0$, $\beta < 1$ and $\delta \ge 0$, and define the dual branches
$V^\#_{\alpha\delta}(y) = (2\alpha\delta - 1 + \alpha\delta y)/(2\alpha + 1 + \alpha y)$ and
$V^\#_{\beta\delta}(y) = (2\delta - 2\beta\delta - 1 + (\delta - \beta\delta - 1) y)/
(3 - 2\beta + (2 - \beta) y)$. Then $V^\#_{\beta\delta}(-1) \ne V^\#_{\alpha\delta}(-1)$.

Equality would force $\delta = -1$.

Source: Fritz Schweiger, *A Remark on Singular Duals of Moebius Maps*, INTEGERS 24 (2024),
Article A17, Lemma 2 (`integers-2024-A17-lem-2`). -/
public theorem_wanted moebius_dual_endpoint_ne_neg_one (α β δ : ℝ) (hα : 0 < α) (hβ : β < 1)
    (hδ : 0 ≤ δ) :
    let dualαδ : ℝ → ℝ := fun y => (2 * α * δ - 1 + α * δ * y) / (2 * α + 1 + α * y)
    let dualβδ : ℝ → ℝ := fun y =>
      (2 * δ - 2 * β * δ - 1 + (δ - β * δ - 1) * y) / (3 - 2 * β + (2 - β) * y)
    dualβδ (-1) ≠ dualαδ (-1)

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
