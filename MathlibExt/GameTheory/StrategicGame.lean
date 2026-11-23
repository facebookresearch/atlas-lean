/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-!
# Strategic-form games, best responses, and Nash equilibria (Atlas EC12.T01)

A strategic-form game has a set of players `ι`, a nonempty strategy set `S i`
for each player, and a real payoff for each player at each strategy profile
`σ : ∀ i, S i`. Player `i`'s unilateral deviation to `t : S i` is the profile
`Function.update σ i t`. A profile is a (pure) Nash equilibrium when every
player's strategy is a best response to the others. The main theorem says this
holds exactly when no unilateral deviation strictly improves the deviator's
payoff.

No finiteness is assumed: the equivalence holds for arbitrary player and
strategy types. As in Osborne and Rubinstein's definition, every strategy set
must be nonempty, so every game has at least one strategy profile. A mixed
extension is again a `StrategicGame`, whose strategy sets are probability
simplices and whose payoffs are expected payoffs.

## References

* J. F. Nash, "Equilibrium points in n-person games", Proc. Natl. Acad. Sci.
  USA 36 (1950), 48--49.
* M. J. Osborne and A. Rubinstein, *A Course in Game Theory*, MIT Press, 1994,
  Definition 11.1 (strategic game) and Definition 14.1 (Nash equilibrium,
  with the best-response formulation that follows it).
* M. Yildiz, *14.12 Game Theory Lecture Notes, Lectures 3-6*, MIT, 2002,
  Section 2.3, Definitions 12 (best response) and 13 (Nash equilibrium).
-/

namespace MathlibExt.GameTheory

/-- A strategic-form (normal-form) game with player set `ι` and a nonempty
strategy set `S i` for player `i`; a strategy profile is a term of `∀ i, S i`. -/
structure StrategicGame (ι : Type*) (S : ι → Type*) where
  /-- `payoff i σ` is player `i`'s payoff at the strategy profile `σ`. -/
  payoff : ι → (∀ i, S i) → ℝ
  /-- Every player has at least one strategy (Osborne-Rubinstein Def. 11.1). -/
  strategy_nonempty : ∀ i, Nonempty (S i)

namespace StrategicGame

/-- `s` is a best response of player `i` to the profile `σ`: with the other
players' strategies in `σ` held fixed, no strategy `t` of player `i` gives `i`
a higher payoff than `s`. -/
def IsBestResponse {ι : Type*} {S : ι → Type*} [DecidableEq ι]
    (G : StrategicGame ι S) (i : ι) (σ : ∀ j, S j) (s : S i) : Prop :=
  ∀ t : S i, G.payoff i (Function.update σ i t) ≤ G.payoff i (Function.update σ i s)

/-- A (pure-strategy) Nash equilibrium: every player's strategy in `σ` is a
best response to `σ`. -/
def IsNash {ι : Type*} {S : ι → Type*} [DecidableEq ι]
    (G : StrategicGame ι S) (σ : ∀ j, S j) : Prop :=
  ∀ i, G.IsBestResponse i σ (σ i)

/-- A profile is a Nash equilibrium exactly when no unilateral deviation
strictly improves the deviating player's payoff. -/
theorem isNash_iff_not_lt_update {ι : Type*} {S : ι → Type*} [DecidableEq ι]
    (G : StrategicGame ι S) (σ : ∀ j, S j) :
    G.IsNash σ ↔
      ∀ (i : ι) (t : S i), ¬ G.payoff i σ < G.payoff i (Function.update σ i t) := by
  simp only [IsNash, IsBestResponse, Function.update_eq_self, not_lt]

/-- Equivalent form: every unilateral deviation gives the deviator at most
their equilibrium payoff. -/
theorem isNash_iff_update_le {ι : Type*} {S : ι → Type*} [DecidableEq ι]
    (G : StrategicGame ι S) (σ : ∀ j, S j) :
    G.IsNash σ ↔
      ∀ (i : ι) (t : S i), G.payoff i (Function.update σ i t) ≤ G.payoff i σ := by
  simp only [IsNash, IsBestResponse, Function.update_eq_self]

end StrategicGame

end MathlibExt.GameTheory
