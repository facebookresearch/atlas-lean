/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Dynamics.MoebiusSingularDual

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

The endpoint inequality, central equations and singularity theorem are proved in
`MathlibExt.Dynamics.MoebiusSingularDual`.
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

end

end MetaMathlibExt
