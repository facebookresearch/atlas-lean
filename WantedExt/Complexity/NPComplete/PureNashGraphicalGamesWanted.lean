/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PURE NASH EQUILIBRIUM in graphical games (3-bounded neighbourhood) is NP-complete

Source:
G. Gottlob, G. Greco and F. Scarcello, "Pure Nash equilibria: hard and easy games", Journal of
Artificial Intelligence Research 24 (2005), 357-406, doi:10.1613/jair.1683, Theorem 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import Batteries.Data.List.Basic
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.StrategicGame

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PureNashGraphicalGames

/-!
# PURE NASH EQUILIBRIUM in graphical games (3-bounded neighbourhood) is NP-complete

A game is a tuple `⟨P, Neigh, Act, U⟩`: a non-empty set `P` of players; for each player `p` a
set `Neigh(p) ⊆ P - {p}` of neighbours and a set `Act(p)` of actions; and for each player `p` a
utility function `u_p : Act(p) × ∏_{j ∈ Neigh(p)} Act(j) → ℝ`. The game is in graphical normal
form (GNF) when each `u_p` is given by a table with a cell for each combined strategy of `p`
and its neighbours, and it has 3-bounded neighbourhood when `|Neigh(p)| ≤ 3` for every player
`p`. INSTANCE: a game in GNF with 3-bounded neighbourhood. QUESTION: does the game have a pure
Nash equilibrium, i.e. a global strategy `x` such that no player `p` can increase `u_p` by
changing only its own action?

The players are `0, …, n - 1` and player `p`'s actions are `0, …, |Act(p)| - 1`. Player `p` is
given by `|Act(p)|`, the list of its neighbours, and its table: a list of cells, each a combined
strategy of `p` and its neighbours (the actions of `p` and of its neighbours, in the order
`p, Neigh(p)`) together with `p`'s utility for it; every combined strategy has exactly one cell.
Utilities are natural numbers: comparisons inside one player's table, which are all that a
pure Nash equilibrium depends on, are preserved by scaling a finite table of rationals to
integers and adding a constant. The game is a `MathlibExt.GameTheory.StrategicGame` with these
payoffs, and the question is `StrategicGame.IsNash`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PURE NASH EQUILIBRIUM in graphical games (3-bounded neighbourhood) is NP-complete.**
Source: Gottlob, Greco and Scarcello (2005), Theorem 3.1. -/
public theorem_wanted pureNashGraphicalGames_npComplete :
    pureNashGraphicalGamesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pureNashGraphicalGamesDec

end MetaMathlibExt.Complexity.NPComplete.PureNashGraphicalGames
