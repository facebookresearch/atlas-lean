/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.PotentialGame
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-! # The revelation principle

A *mechanism* gives each agent `i` a set of actions `X i` and maps every action profile
`x : ∀ i, X i` to an outcome `g x : O`; agent `i` has a private type `θᵢ : Θ i` and a utility
for outcomes. Monetary transfers are part of the outcome: in a quasi-linear setting one takes
`O = A × (ι → ℝ)` (an alternative and a payment vector) and `u i θᵢ (a, p) = vᵢ(θᵢ, a) - p i`.
A *direct* mechanism is one with `X i = Θ i`: agents report types, and it is
*incentive compatible* when truthful reporting is an equilibrium.

The revelation principle says that every equilibrium of every mechanism is reproduced, outcome
for outcome, by the truthful equilibrium of an incentive-compatible direct mechanism: the direct
mechanism `θ ↦ g (fun j ↦ s j (θ j))` asks for types and plays the equilibrium strategies `s` on
the agents' behalf. An agent who could gain by lying to it could have gained by deviating to the
corresponding action in the original mechanism.

## Main results

* `revelationPrinciple_dominantStrategy`: the dominant-strategy revelation principle
  (Nisan 2007, Proposition 9.25).
* `revelationPrinciple_bayesNash`: the Bayesian revelation principle for finite type spaces
  and pure strategies (Myerson 1979, Theorem 2; Myerson 1981, Lemma 1).
* `isPureNash_of_isDominantStrategyProfile`, `isBayesNash_of_isDominantStrategyProfile`: a
  profile of dominant strategies is a pure Nash equilibrium of the complete-information game at
  every type profile, and a Bayesian Nash equilibrium for every prior in a private-values model;
  likewise `isBayesIncentiveCompatible_of_isDominantStrategyIncentiveCompatible` for direct
  mechanisms.

The Bayesian predicates `IsBayesNash` and `IsBayesIncentiveCompatible` take a prior `p` on type
profiles with proofs `hp : ∀ θ, 0 ≤ p θ` and `hp1 : ∑ θ, p θ = 1`. Without them the zero prior
would make every strategy profile an equilibrium and every mechanism incentive compatible, and a
negative prior would reverse preferences. The interim utility `interimUtility` is an
unnormalised weighted sum and is defined for every weight function.

## References

* R. B. Myerson, "Incentive compatibility and the bargaining problem", *Econometrica* 47(1)
  (1979), 61–73, §2 (definition (6)) and §3, Theorem 2.
* R. B. Myerson, "Optimal auction design", *Math. Oper. Res.* 6(1) (1981), 58–73, Lemma 1.
* N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of
  N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*,
  Cambridge University Press, 2007, Definitions 9.24 and 9.15, Proposition 9.25.
-/

namespace MathlibExt.GameTheory.MechanismDesign

open Finset

variable {ι : Type*} [DecidableEq ι] {Θ : ι → Type*} {X : ι → Type*} {O : Type*}

/-- **Dominant-strategy profile.** In the mechanism `g`, with private-value utilities
`u i θᵢ o`, the strategy profile `s` (agent `i` of type `θᵢ` plays `s i θᵢ`) is a profile of
dominant strategies: whatever the others play, `s i θᵢ` is a best action for agent `i` of type
`θᵢ` (Nisan 2007, Definition 9.24 and the definition of dominant-strategy implementation in
§9.4.2). -/
def IsDominantStrategyProfile (u : ∀ i, Θ i → O → ℝ) (g : (∀ i, X i) → O)
    (s : ∀ i, Θ i → X i) : Prop :=
  ∀ i (θi : Θ i) (x : ∀ j, X j) (a : X i),
    u i θi (g (Function.update x i a)) ≤ u i θi (g (Function.update x i (s i θi)))

/-- **Dominant-strategy incentive compatibility.** The direct mechanism `f`, which maps each
profile of reported types to an outcome, is dominant-strategy incentive compatible
(strategy-proof): truthful reporting is optimal for every agent whatever the others report
(Nisan 2007, Definition 9.15, with payments absorbed into the outcome). -/
def IsDominantStrategyIncentiveCompatible (u : ∀ i, Θ i → O → ℝ) (f : (∀ i, Θ i) → O) :
    Prop :=
  ∀ i (θ : ∀ j, Θ j) (θi' : Θ i), u i (θ i) (f (Function.update θ i θi')) ≤ u i (θ i) (f θ)

/- Playing the strategies `s` on a profile of types in which agent `i` reports `θi'`. -/
private theorem comp_update (s : ∀ i, Θ i → X i) (θ : ∀ j, Θ j) (i : ι) (θi' : Θ i) :
    (fun j => s j (Function.update θ i θi' j)) =
      Function.update (fun j => s j (θ j)) i (s i θi') := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- **Revelation principle (dominant strategies).** If the strategies `s` form a profile of
dominant strategies in the mechanism `g`, then the direct mechanism
`θ ↦ g (fun j ↦ s j (θ j))` is dominant-strategy incentive compatible; by construction its
truthful outcome at every type profile is the equilibrium outcome of `g` (Nisan 2007,
Proposition 9.25; payments are part of the outcome, so they agree as well). -/
theorem revelationPrinciple_dominantStrategy {u : ∀ i, Θ i → O → ℝ}
    {g : (∀ i, X i) → O} {s : ∀ i, Θ i → X i} (hs : IsDominantStrategyProfile u g s) :
    IsDominantStrategyIncentiveCompatible u (fun θ => g (fun j => s j (θ j))) := by
  intro i θ θi'
  have h := hs i (θ i) (fun j => s j (θ j)) (s i θi')
  rw [Function.update_eq_self] at h
  simpa only [comp_update] using h

/-- **Dominant strategies give pure Nash equilibria.** If `s` is a profile of dominant
strategies in the mechanism `g`, then at every type profile `θ` the action profile
`fun j ↦ s j (θ j)` is a pure Nash equilibrium of the complete-information game with costs
`-u i (θ i) (g x)` (`PotentialGame.IsPureNash` is stated for costs). -/
theorem isPureNash_of_isDominantStrategyProfile {u : ∀ i, Θ i → O → ℝ} {g : (∀ i, X i) → O}
    {s : ∀ i, Θ i → X i} (hs : IsDominantStrategyProfile u g s) (θ : ∀ j, Θ j) :
    PotentialGame.IsPureNash (fun i x => -u i (θ i) (g x)) (fun j => s j (θ j)) := by
  intro i a
  have h := hs i (θ i) (fun j => s j (θ j)) a
  rw [Function.update_eq_self] at h
  simpa using h

section Bayes

variable [Fintype ι] [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]

/-- **Interim expected utility.** For a prior `p` on the finite set of type profiles and
utilities `u i θ o` that may depend on the whole type profile, the expected utility of agent
`i` of type `θi` when each profile `θ` leads to the outcome `h θ`:
`∑_{θ : θ i = θi} p θ · u i θ (h θ)`. This is Myerson's `Zᵢ` (1979, equation (5)) multiplied
by the marginal probability of `θi`, so the incentive constraints below are those of
Myerson (1979, (6)) whenever that marginal is positive, and are vacuous when it is zero. -/
def interimUtility (p : (∀ j, Θ j) → ℝ) (u : ι → (∀ j, Θ j) → O → ℝ) (i : ι) (θi : Θ i)
    (h : (∀ j, Θ j) → O) : ℝ :=
  ∑ θ ∈ univ.filter (fun θ : ∀ j, Θ j => θ i = θi), p θ * u i θ (h θ)

/-- **Bayesian Nash equilibrium.** For a prior `p` on type profiles (`p ≥ 0`, `∑ p = 1`), the
pure strategy profile `s` is a Bayesian Nash equilibrium of the mechanism `g` for the prior `p`
and the utilities `u`: no agent of any type gains in interim expectation by a unilateral
deviation to another action, the others following `s` (Myerson 1979, (14), restricted to pure
response plans). The prior must be a probability distribution: under the zero prior every
profile would be an equilibrium. -/
def IsBayesNash (p : (∀ j, Θ j) → ℝ) (_hp : ∀ θ, 0 ≤ p θ) (_hp1 : ∑ θ, p θ = 1)
    (u : ι → (∀ j, Θ j) → O → ℝ) (g : (∀ i, X i) → O) (s : ∀ i, Θ i → X i) : Prop :=
  ∀ i (θi : Θ i) (a : X i),
    interimUtility p u i θi (fun θ => g (Function.update (fun j => s j (θ j)) i a)) ≤
      interimUtility p u i θi (fun θ => g (fun j => s j (θ j)))

/-- **Bayesian incentive compatibility.** For a prior `p` on type profiles (`p ≥ 0`,
`∑ p = 1`), the direct mechanism `f` is Bayesian incentive compatible: truthful reporting is a
Bayesian Nash equilibrium, that is, no agent of any type `θi` gains in interim expectation by
reporting `θi'` while the others report truthfully (Myerson 1979, (6); Myerson 1981, (3.5);
Myerson and Satterthwaite 1983, §2). The prior must be a probability distribution: under the
zero prior every mechanism would be incentive compatible. -/
def IsBayesIncentiveCompatible (p : (∀ j, Θ j) → ℝ) (_hp : ∀ θ, 0 ≤ p θ) (_hp1 : ∑ θ, p θ = 1)
    (u : ι → (∀ j, Θ j) → O → ℝ) (f : (∀ i, Θ i) → O) : Prop :=
  ∀ i (θi θi' : Θ i),
    interimUtility p u i θi (fun θ => f (Function.update θ i θi')) ≤
      interimUtility p u i θi f

/-- **Revelation principle (Bayesian, pure strategies).** If the pure strategies `s` form a
Bayesian Nash equilibrium of the mechanism `g`, then the direct mechanism
`θ ↦ g (fun j ↦ s j (θ j))` is Bayesian incentive compatible, and by construction its truthful
outcome at every type profile is the equilibrium outcome of `g`, so every type of every agent
gets the same interim utility (Myerson 1979, Theorem 2; Myerson 1981, Lemma 1). Myerson's
Theorem 2 also allows randomized response plans (mixed strategies); this statement covers pure
strategies only, with an arbitrary outcome set `O`, which may itself be a set of lotteries. -/
theorem revelationPrinciple_bayesNash {p : (∀ j, Θ j) → ℝ} {hp : ∀ θ, 0 ≤ p θ}
    {hp1 : ∑ θ, p θ = 1} {u : ι → (∀ j, Θ j) → O → ℝ} {g : (∀ i, X i) → O}
    {s : ∀ i, Θ i → X i} (hs : IsBayesNash p hp hp1 u g s) :
    IsBayesIncentiveCompatible p hp hp1 u (fun θ => g (fun j => s j (θ j))) := by
  intro i θi θi'
  have h := hs i θi (s i θi')
  have hcongr : ∀ θ ∈ univ.filter (fun θ : ∀ j, Θ j => θ i = θi),
      p θ * u i θ (g (fun j => s j (Function.update θ i θi' j))) =
        p θ * u i θ (g (Function.update (fun j => s j (θ j)) i (s i θi'))) := by
    intro θ _
    rw [comp_update]
  unfold interimUtility at h ⊢
  rw [Finset.sum_congr rfl hcongr]
  exact h

/-- **Dominant strategies are Bayesian Nash.** In a private-values model (agent `i`'s utility
`w i (θ i) o` depends only on its own type), a profile of dominant strategies is a Bayesian
Nash equilibrium for every prior `p`. -/
theorem isBayesNash_of_isDominantStrategyProfile {w : ∀ i, Θ i → O → ℝ} {g : (∀ i, X i) → O}
    {s : ∀ i, Θ i → X i} (hs : IsDominantStrategyProfile w g s) {p : (∀ j, Θ j) → ℝ}
    (hp : ∀ θ, 0 ≤ p θ) (hp1 : ∑ θ, p θ = 1) :
    IsBayesNash p hp hp1 (fun i θ => w i (θ i)) g s := by
  intro i θi a
  unfold interimUtility
  refine Finset.sum_le_sum fun θ _ => ?_
  have h := hs i (θ i) (fun j => s j (θ j)) a
  rw [Function.update_eq_self] at h
  exact mul_le_mul_of_nonneg_left h (hp θ)

/-- **Strategy-proof mechanisms are Bayesian incentive compatible.** In a private-values model,
a dominant-strategy incentive-compatible direct mechanism is Bayesian incentive compatible for
every prior `p`. -/
theorem isBayesIncentiveCompatible_of_isDominantStrategyIncentiveCompatible
    {w : ∀ i, Θ i → O → ℝ} {f : (∀ i, Θ i) → O} (hf : IsDominantStrategyIncentiveCompatible w f)
    {p : (∀ j, Θ j) → ℝ} (hp : ∀ θ, 0 ≤ p θ) (hp1 : ∑ θ, p θ = 1) :
    IsBayesIncentiveCompatible p hp hp1 (fun i θ => w i (θ i)) f := by
  intro i θi θi'
  unfold interimUtility
  exact Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left (hf i θ θi') (hp θ)

end Bayes

end MathlibExt.GameTheory.MechanismDesign
