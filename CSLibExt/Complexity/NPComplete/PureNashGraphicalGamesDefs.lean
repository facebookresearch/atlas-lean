/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PURE NASH EQUILIBRIUM in graphical games (3-bounded neighbourhood): definitions

Source:
G. Gottlob, G. Greco and F. Scarcello, "Pure Nash equilibria: hard and easy games", Journal of
Artificial Intelligence Research 24 (2005), 357-406, doi:10.1613/jair.1683, Theorem 3.1.
-/
module

public import Batteries.Data.List.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.StrategicGame

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PureNashGraphicalGames

/-- An instance: for each player `p`, the number `|Act(p)|` of actions, the list `Neigh(p)` of
neighbours, and the utility table (combined strategy of `p` and its neighbours, utility). -/
abbrev PureNashGraphicalGamesInstance := List (ℕ × List ℕ × List (List ℕ × ℕ))

/-- The number of actions of player `q`. -/
def numActions (i : PureNashGraphicalGamesInstance) (q : ℕ) : ℕ := (i.getD q (0, [], [])).1

/-- The neighbours of player `q`. -/
def neighbours (i : PureNashGraphicalGamesInstance) (q : ℕ) : List ℕ :=
  (i.getD q (0, [], [])).2.1

/-- The utility table of player `q`. -/
def table (i : PureNashGraphicalGamesInstance) (q : ℕ) : List (List ℕ × ℕ) :=
  (i.getD q (0, [], [])).2.2

/-- The players whose actions player `p`'s utility depends on: `p`, then its neighbours. -/
def scope (i : PureNashGraphicalGamesInstance) (p : ℕ) : List ℕ := p :: neighbours i p

/-- All combined strategies of `p` and its neighbours, as action lists in the order of
`scope i p`. -/
def combinedStrategies (i : PureNashGraphicalGamesInstance) (p : ℕ) : List (List ℕ) :=
  ((scope i p).map fun q => List.range (numActions i q)).sections

/-- Well-formedness of an instance: there is at least one player; every player has at least one
action and at most three neighbours, which are distinct other players; and every player's table
has exactly one cell for each combined strategy of the player and its neighbours. -/
def WellFormed (i : PureNashGraphicalGamesInstance) : Prop :=
  i ≠ [] ∧ ∀ p < i.length, 0 < numActions i p ∧ (neighbours i p).Nodup ∧
    (∀ q ∈ neighbours i p, q < i.length ∧ q ≠ p) ∧ (neighbours i p).length ≤ 3 ∧
    ((table i p).map Prod.fst).Perm (combinedStrategies i p)

/-- The actions of a global strategy, as natural numbers indexed by player. -/
def profileActions (i : PureNashGraphicalGamesInstance)
    (σ : ∀ p : Fin i.length, Fin (numActions i p)) (q : ℕ) : ℕ :=
  if h : q < i.length then (σ ⟨q, h⟩ : ℕ) else 0

/-- Player `p`'s utility under the actions `x`: the table cell for the actions of `p` and its
neighbours. -/
def utility (i : PureNashGraphicalGamesInstance) (p : ℕ) (x : ℕ → ℕ) : ℕ :=
  ((table i p).lookup ((scope i p).map x)).getD 0

/-- The instance as a strategic game: player `p` chooses an action in `Fin |Act(p)|` and receives
its table utility. -/
noncomputable def game (i : PureNashGraphicalGamesInstance)
    (h : ∀ p : Fin i.length, 0 < numActions i p) :
    MathlibExt.GameTheory.StrategicGame (Fin i.length) (fun p => Fin (numActions i p)) where
  payoff p σ := (utility i p (profileActions i σ) : ℝ)
  strategy_nonempty p := ⟨⟨0, h p⟩⟩

/-- The game has a pure Nash equilibrium. -/
def PureNashGraphicalGamesFeasible (i : PureNashGraphicalGamesInstance) : Prop :=
  ∃ h : ∀ p : Fin i.length, 0 < numActions i p, ∃ σ, (game i h).IsNash σ

open Classical in
/-- PURE NASH EQUILIBRIUM in graphical games (3-bounded neighbourhood) as a decision problem
over bitstrings. -/
noncomputable def pureNashGraphicalGamesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PureNashGraphicalGamesInstance) x with
  | some i => decide (WellFormed i ∧ PureNashGraphicalGamesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PureNashGraphicalGames
