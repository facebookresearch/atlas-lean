/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainPoincare

/-- Boundary check: at time `0` the decay bound is the trivial
identity factor `1`. -/
example {α : Type*} [Fintype α] {K : α → α → ℝ} {π : α → ℝ} {gap : ℝ}
    (hK_nonneg : ∀ x y, 0 ≤ K x y) (hK_sum : ∀ x, ∑ y, K x y = 1)
    (hπ_nonneg : ∀ x, 0 ≤ π x) (hπ_sum : ∑ x, π x = 1)
    (hstat : ∀ y, ∑ x, π x * K x y = π y)
    (hcontract : ∀ f : α → ℝ, piVar π (applyK K f) ≤ (1 - gap) ^ 2 * piVar π f)
    (f : α → ℝ) :
    piVar π (applyKIter K 0 f) ≤ ((1 - gap) ^ 2) ^ 0 * piVar π f :=
  piVar_decay hK_nonneg hK_sum hπ_nonneg hπ_sum hstat hcontract f 0

/-- The zero-step evolution is the identity. -/
example {α : Type*} [Fintype α] (K : α → α → ℝ) (f : α → ℝ) :
    applyKIter K 0 f = f := rfl
