/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.DeficiencyZero.StabilityComposition
public import Domains.Biology.Dynamics.ComplexBalancedStability

/-!
# Deficiency-zero local asymptotic stability

Compose the deficiency-zero result with the complex-balanced stability theorems.
-/

@[expose] public section

open MathlibExt.Biology.Dynamics.ComplexBalanced

namespace DomainsTest.Biology.Dynamics.DeficiencyZero

theorem localAsymptoticStability {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (hδ : N.deficiency = 0)
    (hwr : N.IsWeaklyReversible) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {x₀ : S → ℝ} (hx₀ : ∀ s, 0 < x₀ s) :
    (∃! x : S → ℝ, (∀ s, 0 < x s) ∧ x - x₀ ∈ N.stoichiometricSubspace ∧
      N.massActionField k x = 0) ∧
      ∀ xstar : S → ℝ, (∀ s, 0 < xstar s) →
        xstar - x₀ ∈ N.stoichiometricSubspace → N.massActionField k xstar = 0 →
          (∃ η > 0, ∀ z : S → ℝ,
          z - xstar ∈ N.stoichiometricSubspace → ‖z - xstar‖ < η →
            ∃ x : ℝ → S → ℝ, x 0 = z ∧
              ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t) ∧
          (∀ ε > 0, ∃ η > 0, ∀ x : ℝ → S → ℝ,
          (∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t) →
            x 0 - xstar ∈ N.stoichiometricSubspace → ‖x 0 - xstar‖ < η →
              ∀ t, 0 ≤ t → ‖x t - xstar‖ < ε) ∧
          (∃ η > 0, ∀ x : ℝ → S → ℝ,
          (∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t) →
            x 0 - xstar ∈ N.stoichiometricSubspace → ‖x 0 - xstar‖ < η →
              Filter.Tendsto x Filter.atTop (nhds xstar)) := by
  exact Domains.Biology.Dynamics.DeficiencyZero.localAsymptoticStability_of_stability
    Domains.Biology.Dynamics.ComplexBalancedStability.exists_solution_of_near
    Domains.Biology.Dynamics.ComplexBalancedStability.stable
    Domains.Biology.Dynamics.ComplexBalancedStability.attractive N hδ hwr hk hx₀

end DomainsTest.Biology.Dynamics.DeficiencyZero

#print axioms DomainsTest.Biology.Dynamics.DeficiencyZero.localAsymptoticStability
