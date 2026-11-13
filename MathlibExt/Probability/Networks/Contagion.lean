/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import MathlibExt.Probability.ProbabilityMassFunction.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Algebra.Group.Indicator
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Latent homophily and contagion with an observed tie

A finite witness motivated by Shalizi and Thomas: two potential-outcome
mechanisms over a dyad with explicit traits, a trait-driven tie, and behavior
at two time points. The homophily mechanism (peer behavior from its own trait
and shared environment, no contagion) and the contagion mechanism (peer
behavior from ego behavior through the tie) induce the same joint law on the
observed triple (tie, ego behavior, peer behavior) but different average
effects, so the effect is not identified by the observed law.

## References

- C. R. Shalizi and A. C. Thomas, "Homophily and Contagion Are Generically
  Confounded in Observational Social Network Studies",
  *Sociological Methods & Research* 40(2) (2011), 211-239 (arXiv:1004.4704).
-/

@[expose] public section

namespace MathlibExt.Probability.Networks

/-- Ego trait (first latent coordinate). -/
def traitEgo : Bool × Bool × Bool → Bool := fun ω => ω.1

/-- Peer trait (second latent coordinate). -/
def traitPeer : Bool × Bool × Bool → Bool := fun ω => ω.2.1

/-- Observed tie from the selection rule: present exactly when ego and peer
traits agree. -/
def tie : Bool × Bool × Bool → Bool := fun ω => ω.1 == ω.2.1

/-- Ego behavior at the earlier time: ego trait masked by shared environment. -/
def egoBehavior : Bool × Bool × Bool → Bool := fun ω => ω.1 ^^ ω.2.2

/-- Homophily mechanism: peer behavior from peer trait and shared environment. -/
def homophilyOutcome : Bool × Bool × Bool → ℝ :=
  fun ω => if ω.2.1 ^^ ω.2.2 then 1 else 0

/-- Contagion mechanism: peer behavior had ego not acted, through the tie. -/
def contagionOutcome₀ : Bool × Bool × Bool → ℝ := fun ω =>
  if egoBehavior ω then (if tie ω then 0 else -1) else (if tie ω then 0 else 1)

/-- Contagion mechanism: peer behavior had ego acted, through the tie. -/
def contagionOutcome₁ : Bool × Bool × Bool → ℝ := fun ω =>
  if egoBehavior ω then (if tie ω then 1 else 0) else (if tie ω then 1 else 2)

/-- Observed triple: tie, ego behavior at the earlier time, and peer observed
behavior at the later time. -/
noncomputable def observationMap {Ω : Type*} (A : Ω → Bool) (D : Ω → Bool)
    (Y₀ Y₁ : Ω → ℝ) : Ω → Bool × Bool × ℝ :=
  fun ω =>
    (A ω, D ω, MathlibExt.Probability.Causality.observed {ω | D ω = true} Y₀ Y₁ ω)

/-- Joint law of the observed triple under the pushforward of `μ`. -/
noncomputable def observedLaw {Ω : Type*} (μ : PMF Ω) (A : Ω → Bool)
    (D : Ω → Bool) (Y₀ Y₁ : Ω → ℝ) : PMF (Bool × Bool × ℝ) :=
  μ.map (observationMap A D Y₀ Y₁)

private theorem obs_homophily_apply (ω : Bool × Bool × Bool) :
    observationMap tie egoBehavior homophilyOutcome homophilyOutcome ω =
      (tie ω, egoBehavior ω, homophilyOutcome ω) := by
  obtain ⟨a, b, c⟩ := ω
  cases a <;> cases b <;> cases c <;>
    simp [observationMap, tie, egoBehavior, homophilyOutcome,
      MathlibExt.Probability.Causality.observed]

private theorem obs_contagion_apply (ω : Bool × Bool × Bool) :
    observationMap tie egoBehavior contagionOutcome₀ contagionOutcome₁ ω =
      (tie ω, egoBehavior ω, homophilyOutcome ω) := by
  obtain ⟨a, b, c⟩ := ω
  cases a <;> cases b <;> cases c <;>
    simp [observationMap, tie, egoBehavior, homophilyOutcome,
      contagionOutcome₀, contagionOutcome₁,
      MathlibExt.Probability.Causality.observed]

/-- Both mechanisms induce the same observation map. -/
theorem observationMap_homophily_eq_contagion :
    observationMap tie egoBehavior homophilyOutcome homophilyOutcome =
      observationMap tie egoBehavior contagionOutcome₀ contagionOutcome₁ := by
  funext ω
  rw [obs_homophily_apply, obs_contagion_apply]

/-- Both mechanisms induce the same observed law. -/
theorem homophily_contagion_same_observedLaw :
    observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
        homophilyOutcome homophilyOutcome =
      observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
        contagionOutcome₀ contagionOutcome₁ := by
  unfold observedLaw
  rw [observationMap_homophily_eq_contagion]

private theorem card_latent : Fintype.card (Bool × Bool × Bool) = 8 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]

private theorem eight_inv_add : (8⁻¹ + 8⁻¹ : ENNReal) = 4⁻¹ := by
  have h8 : (8 : ENNReal) = 2 * 4 := by norm_num
  have h2ne0 : (2 : ENNReal) ≠ 0 := by simp
  have h2netop : (2 : ENNReal) ≠ ⊤ := by simp
  rw [← two_mul, h8, ENNReal.mul_inv (Or.inl h2ne0) (Or.inl h2netop),
    ← mul_assoc, ENNReal.mul_inv_cancel h2ne0 h2netop, one_mul]

/-- Observed law: mass `4⁻¹` where the tie matches ego and peer behavior, `0`
elsewhere. -/
theorem observedLaw_homophily_apply (t d : Bool) (y : ℝ) :
    observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
        homophilyOutcome homophilyOutcome (t, d, y) =
      if y = (if d then (if t then 1 else 0) else (if t then 0 else 1)) then 4⁻¹
        else 0 := by
  simp only [observedLaw, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Fintype.sum_bool, obs_homophily_apply]
  cases t <;> cases d <;>
    by_cases hy1 : y = (1 : ℝ) <;> by_cases hy0 : y = (0 : ℝ) <;>
      simp [hy1, hy0, tie, egoBehavior, homophilyOutcome,
        PMF.uniformFintype_apply, eight_inv_add]

/-- Homophily mechanism: the average effect is zero. -/
theorem ate_homophily :
    MathlibExt.Probability.Causality.ate homophilyOutcome homophilyOutcome
      = 0 := by
  simp [MathlibExt.Probability.Causality.ate,
    MathlibExt.Probability.Causality.popMean]

/-- Contagion mechanism: the average effect is one. -/
theorem ate_contagion :
    MathlibExt.Probability.Causality.ate contagionOutcome₀ contagionOutcome₁
      = 1 := by
  have h : ∀ ω : Bool × Bool × Bool,
      contagionOutcome₁ ω - contagionOutcome₀ ω = 1 := by
    intro ω
    obtain ⟨a, b, c⟩ := ω
    cases a <;> cases b <;> cases c <;>
      simp [contagionOutcome₀, contagionOutcome₁, egoBehavior, tie] <;> norm_num
  simp only [MathlibExt.Probability.Causality.ate,
    MathlibExt.Probability.Causality.popMean]
  rw [Finset.sum_congr rfl (fun ω _ => h ω), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_latent]
  norm_num

/-- Finite witness motivated by Shalizi and Thomas: same observed law,
different average effects. -/
theorem ate_not_identified :
    observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
          homophilyOutcome homophilyOutcome =
        observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
          contagionOutcome₀ contagionOutcome₁ ∧
      MathlibExt.Probability.Causality.ate homophilyOutcome homophilyOutcome ≠
        MathlibExt.Probability.Causality.ate contagionOutcome₀
          contagionOutcome₁ := by
  refine ⟨homophily_contagion_same_observedLaw, ?_⟩
  simp [ate_homophily, ate_contagion]

/-- No function of the observed law recovers the average effect in both
mechanisms. -/
theorem ate_not_recoverable (f : PMF (Bool × Bool × ℝ) → ℝ) :
    ¬ (f (observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
          homophilyOutcome homophilyOutcome) =
        MathlibExt.Probability.Causality.ate homophilyOutcome homophilyOutcome ∧
      f (observedLaw (PMF.uniformFintype (Bool × Bool × Bool)) tie egoBehavior
          contagionOutcome₀ contagionOutcome₁) =
        MathlibExt.Probability.Causality.ate contagionOutcome₀
          contagionOutcome₁) := by
  rintro ⟨hH, hC⟩
  rw [ate_homophily] at hH
  rw [ate_contagion] at hC
  rw [homophily_contagion_same_observedLaw] at hH
  rw [hH] at hC
  exact zero_ne_one hC

end MathlibExt.Probability.Networks
