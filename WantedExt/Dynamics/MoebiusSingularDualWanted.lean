/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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
