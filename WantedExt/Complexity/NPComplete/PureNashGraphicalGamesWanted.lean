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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PureNashGraphicalGamesDefs

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
Utilities are natural numbers. This loses no generality for real utilities: a pure Nash
equilibrium depends only on comparisons between entries of one player's table, and replacing
each entry of a finite table by its rank among the table's distinct values (equal payoffs get
equal ranks) preserves every such comparison. The game is a
`MathlibExt.GameTheory.StrategicGame` with these payoffs, and the question is
`StrategicGame.IsNash`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PURE NASH EQUILIBRIUM in graphical games (3-bounded neighbourhood) is NP-complete.**
Source: Gottlob, Greco and Scarcello (2005), Theorem 3.1. -/
public theorem_wanted pureNashGraphicalGames_npComplete :
    pureNashGraphicalGamesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pureNashGraphicalGamesDec

end MetaMathlibExt.Complexity.NPComplete.PureNashGraphicalGames
