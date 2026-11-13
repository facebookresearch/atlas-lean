/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Networks.Contagion

import Mathlib.Algebra.Group.Indicator
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Boundary tests for latent homophily versus contagion

Boundary checks for `MathlibExt.Probability.Networks.Contagion`: spot values
of the contagion observed law, the statistical association in the joint law,
non-recovery of the latent traits from the observed triple, the extended
observation (with both traits revealed) whose law still coincides across the
two mechanisms, and the contagion effect: one on the tie and zero off it.

## References

- C. R. Shalizi and A. C. Thomas, "Homophily and Contagion Are Generically
  Confounded in Observational Social Network Studies",
  *Sociological Methods & Research* 40(2) (2011), 211-239 (arXiv:1004.4704).
-/

open MathlibExt.Probability.Networks

@[expose] public section

namespace MathlibExt.Probability.Networks.ContagionTest

/-- Contagion law: mass `4⁻¹` at `(true, true, 1)`. -/
theorem contagion_law_true_true_one :
    observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
        contagionOutcome₀ contagionOutcome₁ (true, true, 1) = 4⁻¹ := by
  simp [← homophily_contagion_same_observedLaw, observedLaw_homophily_apply]

/-- Contagion law: mass `4⁻¹` at `(false, false, 1)`. -/
theorem contagion_law_false_false_one :
    observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
        contagionOutcome₀ contagionOutcome₁ (false, false, 1) = 4⁻¹ := by
  simp [← homophily_contagion_same_observedLaw, observedLaw_homophily_apply]

/-- Contagion law: mass `0` at `(true, true, 0)`. -/
theorem contagion_law_true_true_zero :
    observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
        contagionOutcome₀ contagionOutcome₁ (true, true, 0) = 0 := by
  simp [← homophily_contagion_same_observedLaw, observedLaw_homophily_apply]

/-- Contagion law: mass `0` at `(false, true, 1)`. -/
theorem contagion_law_false_true_one :
    observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
        contagionOutcome₀ contagionOutcome₁ (false, true, 1) = 0 := by
  simp [← homophily_contagion_same_observedLaw, observedLaw_homophily_apply]

/-- Association: positive mass at `(true, true, 1)`. -/
theorem association_pos_true_true_one :
    0 < observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
      homophilyOutcome homophilyOutcome (true, true, 1) := by
  rw [observedLaw_homophily_apply]
  simp

/-- Association: zero mass at `(true, true, 0)`. -/
theorem association_zero_true_true_zero :
    observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
        homophilyOutcome homophilyOutcome (true, true, 0) = 0 := by
  simp [observedLaw_homophily_apply]

/-- Association: positive mass at `(false, false, 1)`. -/
theorem association_pos_false_false_one :
    0 < observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
      homophilyOutcome homophilyOutcome (false, false, 1) := by
  rw [observedLaw_homophily_apply]
  simp

/-- Association: zero mass at `(false, true, 1)`. -/
theorem association_zero_false_true_one :
    observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
        homophilyOutcome homophilyOutcome (false, true, 1) = 0 := by
  simp [observedLaw_homophily_apply]

/-- The ego trait is not determined by the observed triple. -/
theorem traitEgo_not_recovered :
    ∃ ω₁ ω₂,
      observationMap tie egoBehavior homophilyOutcome homophilyOutcome ω₁ =
          observationMap tie egoBehavior homophilyOutcome homophilyOutcome ω₂ ∧
        traitEgo ω₁ ≠ traitEgo ω₂ := by
  refine ⟨(true, true, false), (false, false, true), ?_, ?_⟩
  · simp [observationMap, tie, egoBehavior, homophilyOutcome,
      MathlibExt.Probability.Causality.observed]
  · simp [traitEgo]

/-- The peer trait is not determined by the observed triple. -/
theorem traitPeer_not_recovered :
    ∃ ω₁ ω₂,
      observationMap tie egoBehavior homophilyOutcome homophilyOutcome ω₁ =
          observationMap tie egoBehavior homophilyOutcome homophilyOutcome ω₂ ∧
        traitPeer ω₁ ≠ traitPeer ω₂ := by
  refine ⟨(true, true, false), (false, false, true), ?_, ?_⟩
  · simp [observationMap, tie, egoBehavior, homophilyOutcome,
      MathlibExt.Probability.Causality.observed]
  · simp [traitPeer]

/-- Extended observation (traits revealed): the laws still coincide. -/
theorem extended_same_observedLaw :
    PMF.map (fun ω => ((traitEgo ω, traitPeer ω),
        observationMap tie egoBehavior homophilyOutcome homophilyOutcome ω))
        (PMF.uniformFintype (Bool × Bool × Bool)) =
      PMF.map (fun ω => ((traitEgo ω, traitPeer ω),
        observationMap tie egoBehavior contagionOutcome₀ contagionOutcome₁ ω))
        (PMF.uniformFintype (Bool × Bool × Bool)) := by
  rw [observationMap_homophily_eq_contagion]

/-- Even with traits revealed, no function of the extended law recovers the
effect. -/
theorem extended_effect_not_recoverable
    (f : PMF ((Bool × Bool) × (Bool × Bool × ℝ)) → ℝ) :
    ¬ (f (PMF.map (fun ω => ((traitEgo ω, traitPeer ω),
          observationMap tie egoBehavior homophilyOutcome homophilyOutcome ω))
          (PMF.uniformFintype (Bool × Bool × Bool))) =
        MathlibExt.Probability.Causality.ate homophilyOutcome homophilyOutcome ∧
      f (PMF.map (fun ω => ((traitEgo ω, traitPeer ω),
          observationMap tie egoBehavior contagionOutcome₀ contagionOutcome₁ ω))
          (PMF.uniformFintype (Bool × Bool × Bool))) =
        MathlibExt.Probability.Causality.ate contagionOutcome₀
          contagionOutcome₁) := by
  rintro ⟨hH, hC⟩
  rw [ate_homophily] at hH
  rw [ate_contagion] at hC
  rw [extended_same_observedLaw] at hH
  rw [hH] at hC
  norm_num at hC

/-- No contagion without a tie: off the tie the contagion potential outcomes
agree, so the ego intervention does not move the peer. -/
theorem contagion_no_effect_off_tie (ω : Bool × Bool × Bool) (h : tie ω = false) :
    contagionOutcome₁ ω = contagionOutcome₀ ω := by
  simp [contagionOutcome₀, contagionOutcome₁, h]

/-- On the tie the ego intervention moves the peer by one. -/
theorem contagion_effect_on_tie (ω : Bool × Bool × Bool) (h : tie ω = true) :
    contagionOutcome₁ ω - contagionOutcome₀ ω = 1 := by
  simp [contagionOutcome₀, contagionOutcome₁, h]

/-- The latent states `(true, false, false)` and `(false, true, false)` have no
tie, and their contagion potential outcomes agree. -/
theorem contagion_no_effect_examples :
    tie (true, false, false) = false ∧ tie (false, true, false) = false ∧
      contagionOutcome₁ (true, false, false) = contagionOutcome₀ (true, false, false) ∧
      contagionOutcome₁ (false, true, false) = contagionOutcome₀ (false, true, false) := by
  simp [tie, contagionOutcome₀, contagionOutcome₁]

end MathlibExt.Probability.Networks.ContagionTest
