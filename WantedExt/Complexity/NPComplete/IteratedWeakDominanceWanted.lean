/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IWD-STRATEGY-ELIMINATION (eliminability by iterated weak dominance) is NP-complete

Source:
V. Conitzer and T. Sandholm, "Complexity of (iterated) dominance", Proceedings of the 6th ACM
Conference on Electronic Commerce (EC 2005), 88-97, doi:10.1145/1064009.1064019,
Definition 3 and Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IteratedWeakDominanceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IteratedWeakDominance

/-!
# IWD-STRATEGY-ELIMINATION (eliminability by iterated weak dominance) is NP-complete

A two-player normal-form game: the row player has pure strategies `0, …, m - 1`, the column
player has pure strategies `0, …, n - 1`, and each player has a utility for each pair of pure
strategies. A strategy `σ'` of a player is weakly dominated by a strategy `σ` of the same
player if `σ` gives that player at least the utility of `σ'` against every strategy of the
opponent and strictly more against at least one. In iterated weak dominance, strategies are
eliminated one at a time; at each step the eliminated strategy must be weakly dominated by a
strategy of the same player that has not been eliminated, with the comparison made only
against the opponent's strategies that have not been eliminated. Given a game and a
distinguished pure strategy `σ*`, IWD-STRATEGY-ELIMINATION asks whether some such sequence of
eliminations eliminates `σ*` (Conitzer and Sandholm 2005, Definition 3). Their Theorem 1
proves it NP-complete even with two players and utilities in `{0, 1}`, whether or not
dominance by mixed strategies is allowed; this file states the two-player problem with
dominance by pure strategies and integer utilities.

Utilities are integers, each encoded as a pair of naturals `(positive part, negative part)`
representing their difference, as in `ZeroOneILPWanted`. A state of the elimination is the
pair of sets of strategies not yet eliminated.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **IWD-STRATEGY-ELIMINATION is NP-complete** (two players, dominance by pure strategies).
Source: Conitzer and Sandholm (2005), Theorem 1. -/
public theorem_wanted iteratedWeakDominance_npComplete :
    iteratedWeakDominanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L iteratedWeakDominanceDec

end MetaMathlibExt.Complexity.NPComplete.IteratedWeakDominance
