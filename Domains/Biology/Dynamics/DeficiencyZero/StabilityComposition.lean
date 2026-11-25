/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.DeficiencyZero.Integration
import Domains.Biology.Dynamics.ComplexBalancedStability

/-!
# Local asymptotic stability by composition

The deficiency-zero equilibrium theorems combine with nearby solution existence,
stability, and attraction for complex-balanced systems to give local asymptotic
stability relative to a stoichiometric compatibility class.

`localAsymptoticStability_of_stability` is the composition, with the three complex-balanced
results as hypotheses; `localAsymptoticStability` supplies them from
`Domains.Biology.Dynamics.ComplexBalancedStability`.

Reference: Feinberg (1987), Theorem 6.1.1(iii) and Section 5.2.
-/

@[expose] public section

open MathlibExt.Biology.Dynamics.ComplexBalanced

namespace Domains.Biology.Dynamics.DeficiencyZero

theorem localAsymptoticStability_of_stability {S ρ : Type*} [Fintype S] [Fintype ρ]
    (hCB1 : ∀ (N : ReactionNetwork S ρ) (k : ρ → ℝ), (∀ r, 0 < k r) →
      ∀ cstar : S → ℝ, (∀ s, 0 < cstar s) → N.IsComplexBalanced k cstar →
        ∀ xstar : S → ℝ, (∀ s, 0 < xstar s) → N.massActionField k xstar = 0 →
          ∃ η > 0, ∀ z : S → ℝ,
          z - xstar ∈ N.stoichiometricSubspace → ‖z - xstar‖ < η →
            ∃ x : ℝ → S → ℝ, x 0 = z ∧
              ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t)
    (hCB2 : ∀ (N : ReactionNetwork S ρ) (k : ρ → ℝ), (∀ r, 0 < k r) →
      ∀ cstar : S → ℝ, (∀ s, 0 < cstar s) → N.IsComplexBalanced k cstar →
        ∀ xstar : S → ℝ, (∀ s, 0 < xstar s) → N.massActionField k xstar = 0 →
          ∀ ε > 0, ∃ η > 0, ∀ x : ℝ → S → ℝ,
          (∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t) →
            x 0 - xstar ∈ N.stoichiometricSubspace → ‖x 0 - xstar‖ < η →
              ∀ t, 0 ≤ t → ‖x t - xstar‖ < ε)
    (hCB3 : ∀ (N : ReactionNetwork S ρ) (k : ρ → ℝ), (∀ r, 0 < k r) →
      ∀ cstar : S → ℝ, (∀ s, 0 < cstar s) → N.IsComplexBalanced k cstar →
        ∀ xstar : S → ℝ, (∀ s, 0 < xstar s) → N.massActionField k xstar = 0 →
          ∃ η > 0, ∀ x : ℝ → S → ℝ,
          (∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t) →
            x 0 - xstar ∈ N.stoichiometricSubspace → ‖x 0 - xstar‖ < η →
              Filter.Tendsto x Filter.atTop (nhds xstar))
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
  obtain ⟨cstar, hcstar, hcb⟩ := N.exists_pos_isComplexBalanced hδ hwr hk
  refine ⟨N.existsUnique_equilibrium hδ hwr hk hx₀, ?_⟩
  intro xstar hxstar _ heq
  exact ⟨hCB1 N k hk cstar hcstar hcb xstar hxstar heq,
    hCB2 N k hk cstar hcstar hcb xstar hxstar heq,
    hCB3 N k hk cstar hcstar hcb xstar hxstar heq⟩

/-- **Deficiency-zero theorem, local asymptotic stability.** Let `N` be a weakly reversible
mass-action network of deficiency zero with positive rate constants `k`, and let `x₀` be a
positive state. The stoichiometric compatibility class of `x₀` contains exactly one positive
equilibrium, and every positive equilibrium `xstar` in that class is locally asymptotically
stable relative to the class: every state of the class close enough to `xstar` starts a global
forward solution; for every `ε > 0`, every solution that starts in the class close enough to
`xstar` stays within `ε` of it for all `t ≥ 0`; and every solution that starts in the class
close enough to `xstar` converges to it. Distances are sup-norm distances on `S → ℝ`, and
solutions have two-sided derivatives at every `t ≥ 0`.

Source: Feinberg (1987), Theorem 6.1.1(iii) and Section 5.2. -/
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
              Filter.Tendsto x Filter.atTop (nhds xstar)) :=
  localAsymptoticStability_of_stability
    Domains.Biology.Dynamics.ComplexBalancedStability.exists_solution_of_near
    Domains.Biology.Dynamics.ComplexBalancedStability.stable
    Domains.Biology.Dynamics.ComplexBalancedStability.attractive N hδ hwr hk hx₀

end Domains.Biology.Dynamics.DeficiencyZero
