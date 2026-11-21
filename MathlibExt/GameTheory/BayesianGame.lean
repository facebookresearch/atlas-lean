/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MechanismDesign.RevelationPrinciple
public import MathlibExt.GameTheory.StrategicGame

set_option autoImplicit false

@[expose] public section

/-!
# Finite Bayesian games and the agent normal form

A finite Bayesian game has finite type and action sets, a common prior on type
profiles with positive type marginals, and utilities over type and action
profiles. The equilibrium predicate is the mechanism-design Bayesian Nash
predicate at the identity outcome rule; `condInterim` is its normalized
ex-interim form. The agent (expanded) normal form makes each player-type pair
a player whose payoff is that ex-interim utility.

## Main results

* `BayesianGame.isBayesNash_iff`: equilibrium is ex-interim optimality for
  every type.
* `BayesianGame.isBayesNash_iff_isNash_agentForm`: Bayesian equilibrium is
  Nash equilibrium of the agent form.

## References

* S. Nath, CS 6001 Lecture 12, "Bayesian Games and Bayesian Equilibrium"
  (IIT Bombay), Definitions 12.2, 12.6 and 12.11 and equation (12.9).
* F. Gul, Ec 501 lecture notes, "Bayesian Games" (Princeton).
-/

open scoped BigOperators

namespace MathlibExt.GameTheory

/-- **Bayesian game.** A finite Bayesian game: players `ι`, finite type
sets `Θ i`, action sets `X i`, a common prior on type profiles under which
every type has positive marginal probability, and utilities depending on
the action profile and the type profile. -/
structure BayesianGame (ι : Type*) (Θ X : ι → Type*) [DecidableEq ι] [Fintype ι]
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] where
  /-- The common prior on type profiles. -/
  prior : (∀ i, Θ i) → ℝ
  /-- The prior is nonnegative. -/
  prior_nonneg : ∀ θ, 0 ≤ prior θ
  /-- The prior is a probability distribution. -/
  prior_sum : ∑ θ, prior θ = 1
  /-- Every type has positive marginal probability. -/
  prior_pos : ∀ (i : ι) (θi : Θ i),
    0 < ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = θi), prior θ
  /-- Payoffs: `utility i θ a` is player `i`'s payoff at type profile `θ`
  and action profile `a`. -/
  utility : ι → (∀ j, Θ j) → (∀ i, X i) → ℝ
  /-- Every player has at least one action. -/
  action_nonempty : ∀ i, Nonempty (X i)

namespace BayesianGame

/-- The marginal probability of type `θi` of player `i`. -/
noncomputable def marginal {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι] [Fintype ι]
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] (G : BayesianGame ι Θ X)
    (i : ι) (θi : Θ i) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = θi), G.prior θ

/-- **Ex-interim utility.** The conditional expected utility of type `θi`
of player `i` under the pure strategy profile `s`: the other players'
types are weighted by the conditional distribution given `θi`. -/
noncomputable def condInterim {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι] [Fintype ι]
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] (G : BayesianGame ι Θ X)
    (s : ∀ i, Θ i → X i) (i : ι) (θi : Θ i) : ℝ :=
  (∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = θi),
      G.prior θ * G.utility i θ (fun j => s j (θ j))) / G.marginal i θi

/-- **Bayesian Nash equilibrium.** The pure strategy profile `s` is a
Bayesian Nash equilibrium: no type of any player gains in ex-interim
expectation by a unilateral deviation. This is the mechanism-design
predicate at the identity outcome rule. -/
def IsBayesNash {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι] [Fintype ι]
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] (G : BayesianGame ι Θ X)
    (s : ∀ i, Θ i → X i) : Prop :=
  MathlibExt.GameTheory.MechanismDesign.IsBayesNash G.prior G.prior_nonneg
    G.prior_sum G.utility id s

/-- Read a plan profile as an agent profile: the action of agent
`(i, θi)` is what the plan of player `i` prescribes at type `θi`. -/
def toAgentProfile {ι : Type*} {Θ X : ι → Type*}
    (s : ∀ i, Θ i → X i) : ∀ a : Σ i, Θ i, X a.fst :=
  fun a => s a.fst a.snd

/-- Read an agent profile as a plan profile. -/
def ofAgentProfile {ι : Type*} {Θ X : ι → Type*}
    (σ : ∀ a : Σ i, Θ i, X a.fst) : ∀ i, Θ i → X i :=
  fun i θi => σ ⟨i, θi⟩

/-- The agent profile prescribes the plan's action at each type. -/
theorem toAgentProfile_apply {ι : Type*} {Θ X : ι → Type*}
    (s : ∀ i, Θ i → X i) (i : ι) (θi : Θ i) :
    toAgentProfile s ⟨i, θi⟩ = s i θi :=
  rfl

/-- **The agent (expanded) normal form.** Every pair `(i, θi)` is a
player with action set `X i`; its payoff at an agent profile is the
ex-interim utility of type `θi` under the induced plan profile. -/
noncomputable def agentForm {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι] [Fintype ι]
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] (G : BayesianGame ι Θ X) :
    MathlibExt.GameTheory.StrategicGame (Σ i, Θ i) (fun a => X a.fst) where
  payoff a σ := G.condInterim (ofAgentProfile σ) a.fst a.snd
  strategy_nonempty a := G.action_nonempty a.fst

/-- The marginal probability of every type is positive. -/
theorem marginal_pos {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι] [Fintype ι]
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]
    (G : BayesianGame ι Θ X) (i : ι) (θi : Θ i) :
    0 < G.marginal i θi :=
  G.prior_pos i θi

/-- Updating the realized action profile agrees with the updated plan's profile. -/
theorem update_action_eq {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι]
    (s : ∀ i, Θ i → X i) (i : ι) (a : X i) (θ : ∀ j, Θ j) :
    Function.update (fun j => s j (θ j)) i a =
      (fun j => (Function.update s i (fun _ => a)) j (θ j)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    show Function.update (fun j => s j (θ j)) j a j =
      Function.update s j (fun _ => a) j (θ j)
    rw [Function.update_self, Function.update_self]
  · show Function.update (fun j => s j (θ j)) i a j =
      Function.update s i (fun _ => a) j (θ j)
    rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- The ex-interim utility is the unnormalised interim utility per unit mass. -/
theorem condInterim_eq {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι] [Fintype ι]
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]
    (G : BayesianGame ι Θ X) (s' : ∀ i, Θ i → X i) (i : ι) (θi : Θ i) :
    G.condInterim s' i θi =
      MathlibExt.GameTheory.MechanismDesign.interimUtility G.prior G.utility i θi
        (fun θ => fun j => s' j (θ j)) / G.marginal i θi :=
  rfl

/-- An agent deviation agrees with the plan deviation on filtered profiles. -/
theorem agent_dev_agree {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι]
    [∀ i, DecidableEq (Θ i)] (s : ∀ i, Θ i → X i) (i : ι) (θi : Θ i)
    (t : X i) (θ : ∀ j, Θ j) (hθ : θ i = θi) :
    (fun j => ofAgentProfile (Function.update (toAgentProfile s) ⟨i, θi⟩ t) j (θ j)) =
      (fun j => (Function.update s i (fun _ => t)) j (θ j)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    show Function.update (toAgentProfile s) ⟨j, θi⟩ t ⟨j, θ j⟩ =
      Function.update s j (fun _ => t) j (θ j)
    rw [hθ, Function.update_self, Function.update_self]
  · have hne : (⟨j, θ j⟩ : Σ k, Θ k) ≠ ⟨i, θi⟩ :=
      fun h => hj (congrArg Sigma.fst h)
    show Function.update (toAgentProfile s) ⟨i, θi⟩ t ⟨j, θ j⟩ =
      Function.update s i (fun _ => t) j (θ j)
    rw [Function.update_of_ne hne, Function.update_of_ne hj, toAgentProfile_apply]

/-- The ex-interim utility only depends on the plan over filtered profiles. -/
theorem condInterim_congr {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι] [Fintype ι]
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]
    (G : BayesianGame ι Θ X) {s₁ s₂ : ∀ i, Θ i → X i} (i : ι) (θi : Θ i)
    (h : ∀ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = θi),
      (fun j => s₁ j (θ j)) = (fun j => s₂ j (θ j))) :
    G.condInterim s₁ i θi = G.condInterim s₂ i θi := by
  unfold condInterim
  congr 1
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [h θ hθ]

/-- Converting a plan profile to an agent profile and back is the identity. -/
theorem ofAgentProfile_toAgentProfile {ι : Type*} {Θ X : ι → Type*}
    (s : ∀ i, Θ i → X i) :
    ofAgentProfile (toAgentProfile s) = s :=
  rfl

/-- Converting an agent profile to a plan profile and back is the identity. -/
theorem toAgentProfile_ofAgentProfile {ι : Type*} {Θ X : ι → Type*}
    (σ : ∀ a : Σ i, Θ i, X a.fst) :
    toAgentProfile (ofAgentProfile σ) = σ :=
  rfl

/-- Characterisation via the ex-interim (conditional) utility: `s` is a
Bayesian Nash equilibrium iff no type of any player gains ex-interim by
deviating to a single action. -/
theorem isBayesNash_iff {ι : Type*} {Θ X : ι → Type*} [DecidableEq ι]
    [Fintype ι] [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]
    (G : BayesianGame ι Θ X) (s : ∀ i, Θ i → X i) :
    G.IsBayesNash s ↔ ∀ (i : ι) (θi : Θ i) (a : X i),
      G.condInterim (Function.update s i (fun _ => a)) i θi ≤
        G.condInterim s i θi := by
  show MathlibExt.GameTheory.MechanismDesign.IsBayesNash G.prior G.prior_nonneg
      G.prior_sum G.utility id s ↔ _
  show (∀ (i : ι) (θi : Θ i) (a : X i),
      MathlibExt.GameTheory.MechanismDesign.interimUtility G.prior G.utility i θi
        (fun θ => id (Function.update (fun j => s j (θ j)) i a)) ≤
      MathlibExt.GameTheory.MechanismDesign.interimUtility G.prior G.utility i θi
        (fun θ => id (fun j => s j (θ j)))) ↔ _
  apply forall_congr'
  intro i
  apply forall_congr'
  intro θi
  apply forall_congr'
  intro a
  have hm : 0 < G.marginal i θi := marginal_pos G i θi
  have hdev : (fun θ : ∀ j, Θ j => id (Function.update (fun j => s j (θ j)) i a)) =
      (fun θ => fun j => (Function.update s i (fun _ => a)) j (θ j)) := by
    funext θ
    show id (Function.update (fun j => s j (θ j)) i a) =
      fun j => (Function.update s i (fun _ => a)) j (θ j)
    exact update_action_eq s i a θ
  have hbase : (fun θ : ∀ j, Θ j => id (fun j => s j (θ j))) =
      (fun θ => fun j => s j (θ j)) :=
    rfl
  have e1 : G.condInterim (Function.update s i (fun _ => a)) i θi =
      MathlibExt.GameTheory.MechanismDesign.interimUtility G.prior G.utility i θi
        (fun θ => id (Function.update (fun j => s j (θ j)) i a)) / G.marginal i θi := by
    rw [hdev]
    exact condInterim_eq G (Function.update s i (fun _ => a)) i θi
  have e2 : G.condInterim s i θi =
      MathlibExt.GameTheory.MechanismDesign.interimUtility G.prior G.utility i θi
        (fun θ => id (fun j => s j (θ j))) / G.marginal i θi := by
    rw [hbase]
    exact condInterim_eq G s i θi
  rw [e1, e2]
  exact (div_le_div_iff_of_pos_right hm).symm

/-- **Bayesian equilibrium as Nash of the agent form.** A pure strategy
profile is a Bayesian Nash equilibrium if and only if the corresponding
agent profile is a Nash equilibrium of the expanded game. -/
theorem isBayesNash_iff_isNash_agentForm {ι : Type*} {Θ X : ι → Type*}
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Θ i)]
    [∀ i, DecidableEq (Θ i)] [∀ i, Fintype (X i)] (G : BayesianGame ι Θ X)
    (s : ∀ i, Θ i → X i) :
    G.IsBayesNash s ↔
      MathlibExt.GameTheory.StrategicGame.IsNash G.agentForm
        (toAgentProfile s) := by
  refine (isBayesNash_iff G s).trans ?_
  show _ ↔ ∀ (a : Σ i, Θ i) (t : X a.fst),
      G.condInterim
        (ofAgentProfile (Function.update (toAgentProfile s) a t)) a.fst a.snd ≤
      G.condInterim
        (ofAgentProfile (Function.update (toAgentProfile s) a ((toAgentProfile s) a)))
        a.fst a.snd
  constructor
  · intro h a
    obtain ⟨i, θi⟩ := a
    intro t
    show G.condInterim
        (ofAgentProfile (Function.update (toAgentProfile s) ⟨i, θi⟩ t)) i θi ≤
      G.condInterim
        (ofAgentProfile (Function.update (toAgentProfile s) ⟨i, θi⟩
          ((toAgentProfile s) ⟨i, θi⟩))) i θi
    have hdev : G.condInterim
        (ofAgentProfile (Function.update (toAgentProfile s) ⟨i, θi⟩ t)) i θi =
        G.condInterim (Function.update s i (fun _ => t)) i θi := by
      apply condInterim_congr
      intro θ hθ
      exact agent_dev_agree s i θi t θ (Finset.mem_filter.mp hθ).2
    have hbase : Function.update (toAgentProfile s) ⟨i, θi⟩
        ((toAgentProfile s) ⟨i, θi⟩) = toAgentProfile s :=
      Function.update_eq_self _ _
    rw [hdev, hbase, ofAgentProfile_toAgentProfile]
    exact h i θi t
  · intro h i θi a
    have hnash := h ⟨i, θi⟩ a
    have hdev : G.condInterim
        (ofAgentProfile (Function.update (toAgentProfile s) ⟨i, θi⟩ a)) i θi =
        G.condInterim (Function.update s i (fun _ => a)) i θi := by
      apply condInterim_congr
      intro θ hθ
      exact agent_dev_agree s i θi a θ (Finset.mem_filter.mp hθ).2
    have hbase : Function.update (toAgentProfile s) ⟨i, θi⟩
        ((toAgentProfile s) ⟨i, θi⟩) = toAgentProfile s :=
      Function.update_eq_self _ _
    have hnash' : G.condInterim
        (ofAgentProfile (Function.update (toAgentProfile s) ⟨i, θi⟩ a)) i θi ≤
        G.condInterim
          (ofAgentProfile (Function.update (toAgentProfile s) ⟨i, θi⟩
            ((toAgentProfile s) ⟨i, θi⟩))) i θi :=
      hnash
    rw [hdev, hbase, ofAgentProfile_toAgentProfile] at hnash'
    exact hnash'

end BayesianGame

end MathlibExt.GameTheory
