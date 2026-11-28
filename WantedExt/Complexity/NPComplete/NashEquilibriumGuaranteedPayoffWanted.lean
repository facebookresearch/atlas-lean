/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NASH EQUILIBRIUM WITH GUARANTEED PAYOFF is NP-complete

Source:
V. Conitzer and T. Sandholm, "New complexity results about Nash equilibria", Games and
Economic Behavior 63 (2008), 621-641, doi:10.1016/j.geb.2008.02.015 (technical report version
CMU-CS-02-135, arXiv:cs/0205074, Corollary 4: even in symmetric 2-player games it is NP-hard to
determine whether there exists a Nash equilibrium where player 1 has expected utility at least
`k`);
I. Gilboa and E. Zemel, "Nash and correlated equilibria: some complexity considerations",
Games and Economic Behavior 1 (1989), 80-93, doi:10.1016/0899-8256(89)90006-7;
V. Bilò and M. Mavronicolas, "The complexity of computational problems about Nash equilibria
in symmetric win-lose games", Algorithmica 83 (2021), 447-530, doi:10.1007/s00453-020-00763-6,
arXiv:1907.10468, §2.3 (membership in NP of these decision problems for bimatrix games).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NashEquilibriumGuaranteedPayoffDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NashEquilibriumGuaranteedPayoff

open Convexity MathlibExt.GameTheory.MixedNashExistence

/-!
# NASH EQUILIBRIUM WITH GUARANTEED PAYOFF is NP-complete

INSTANCE: a two-player normal-form game with rational payoff matrices `R` (player 1) and `C`
(player 2), each player having a nonempty finite set of pure strategies, and a rational
number `k`.
QUESTION: is there a (mixed) Nash equilibrium in which player 1's expected payoff is at least
`k`?

Player 1 has the pure strategies `Fin m₁` (rows), player 2 has `Fin m₂` (columns), and the
payoffs of the pure profile `(r, c)` are `R[r][c]` and `C[r][c]`. Mixed strategies, expected
payoffs and Nash equilibria are those of `MathlibExt.GameTheory.MixedNashExistence`
(`Convexity.StdSimplex`, `expectedPayoff`, `IsMixedNash`: no player gains by switching to
another mixed strategy). A rational number `(a - b) / q` is given as `((a, b), q)` with `q > 0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding` (numbers in binary). Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NASH EQUILIBRIUM WITH GUARANTEED PAYOFF is NP-complete.** Source: Conitzer and Sandholm
(2008); Gilboa and Zemel (1989); Bilò and Mavronicolas (2021). -/
public theorem_wanted nashEquilibriumGuaranteedPayoff_npComplete :
    nashEquilibriumGuaranteedPayoffDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nashEquilibriumGuaranteedPayoffDec

end MetaMathlibExt.Complexity.NPComplete.NashEquilibriumGuaranteedPayoff
