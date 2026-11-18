/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MechanismDesign.RevelationPrinciple
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

open MathlibExt.GameTheory.MechanismDesign

/-- Two agents each want the outcome's own coordinate to match their type. -/
noncomputable def matchUtility : ∀ _ : Fin 2, Bool → (Fin 2 → Bool) → ℝ :=
  fun i θi o => if o i = θi then 1 else 0

/-- An indirect mechanism: each agent announces a bit and the outcome flips every bit. -/
def flipMechanism (x : Fin 2 → Bool) : Fin 2 → Bool := fun i => !x i

/-- Announcing the negation of one's type is a dominant strategy in the flip mechanism. -/
theorem flip_isDominant :
    IsDominantStrategyProfile matchUtility flipMechanism (fun _ θi => !θi) := by
  intro i θi x a
  simp only [matchUtility, flipMechanism, Function.update_self]
  cases θi <;> cases a <;> norm_num

/-- The revelation principle turns it into a strategy-proof direct mechanism. -/
example : IsDominantStrategyIncentiveCompatible matchUtility
    (fun θ => flipMechanism (fun j => !θ j)) :=
  revelationPrinciple_dominantStrategy flip_isDominant

/-- The resulting direct mechanism implements the identity outcome rule. -/
example (θ : Fin 2 → Bool) : flipMechanism (fun j => !θ j) = θ := by
  funext i; simp [flipMechanism]

/-- For the uniform prior, the dominant-strategy profile is a Bayesian Nash equilibrium, and the
direct mechanism is Bayesian incentive compatible. -/
example : IsBayesNash (fun _ => (1 / 4 : ℝ)) (fun i θ => matchUtility i (θ i)) flipMechanism
    (fun _ θi => !θi) :=
  isBayesNash_of_isDominantStrategyProfile flip_isDominant fun _ => by norm_num

example : IsBayesIncentiveCompatible (fun _ => (1 / 4 : ℝ)) (fun i θ => matchUtility i (θ i))
    (fun θ => flipMechanism (fun j => !θ j)) :=
  revelationPrinciple_bayesNash (isBayesNash_of_isDominantStrategyProfile flip_isDominant fun _ => by norm_num)

/-- The dominant-strategy profile is a pure Nash equilibrium at every type profile. -/
example (θ : Fin 2 → Bool) :
    MathlibExt.GameTheory.PotentialGame.IsPureNash
      (fun i x => -matchUtility i (θ i) (flipMechanism x)) (fun j => !θ j) :=
  isPureNash_of_isDominantStrategyProfile flip_isDominant θ
