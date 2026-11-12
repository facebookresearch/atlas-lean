/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainConductance

/-- Boundary check: the Cheeger bound instantiates for a
two-state chain and a positive-mass set. -/
example {K : Fin 2 → Fin 2 → ℝ} {π : Fin 2 → ℝ} {gap : ℝ}
    (hK_nonneg : ∀ x y, 0 ≤ K x y) (hK_sum : ∀ x, ∑ y, K x y = 1)
    (hπ_nonneg : ∀ x, 0 ≤ π x) (hπ_sum : ∑ x, π x = 1)
    (hstat : ∀ y, ∑ x, π x * K x y = π y)
    (hrev : ∀ x y, π x * K x y = π y * K y x)
    (hpoincare : ∀ f : Fin 2 → ℝ, gap * piVar π f ≤ dirichletForm K π f)
    (S : Finset (Fin 2)) (hS : ∑ x ∈ S, π x ≤ 1 / 2)
    (hSpos : 0 < ∑ x ∈ S, π x) :
    gap ≤ 2 * conductance K π S :=
  gap_le_two_mul_conductance hK_nonneg hK_sum hπ_nonneg hπ_sum hstat hrev
    hpoincare S hS hSpos
