/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHAPLEY-SHUBIK VOTING POWER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS8] SHAPLEY-SHUBIK VOTING POWER;
Y. Matsui and T. Matsui, "NP-completeness for calculating power indices of weighted majority
games", Theoretical Computer Science 263 (2001), 305-310, doi:10.1016/S0304-3975(00)00251-6
(Theorem 3, problem SS1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShapleyShubikVotingPowerDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShapleyShubikVotingPower

/-!
# SHAPLEY-SHUBIK VOTING POWER is NP-complete

INSTANCE: an ordered set `V = {v₁, ..., vₙ}` of voters, a number of votes `w(vᵢ) ∈ ℤ⁺` for each
voter, and a quota `q ∈ ℤ⁺`. QUESTION: does voter `v₁` have nonzero Shapley-Shubik voting power,
i.e., is there an ordering of the voters in which `v₁` is pivotal: the voters before `v₁` have
fewer than `q` votes in total, and together with `v₁` they have at least `q`?

Voters are `0, ..., n - 1` (voter `v₁` is `0`); an ordering is a list that is a permutation of
`[0, ..., n - 1]`, and `v₁` sits at position `j`. Numbers are in binary encoding (the problem is
NP-complete in the ordinary sense; it is solvable in pseudo-polynomial time).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHAPLEY-SHUBIK VOTING POWER is NP-complete.** Source: Garey and Johnson (1979), [MS8];
Matsui and Matsui (2001). -/
public theorem_wanted shapleyShubikVotingPower_npComplete :
    shapleyShubikVotingPowerDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shapleyShubikVotingPowerDec

end MetaMathlibExt.Complexity.NPComplete.ShapleyShubikVotingPower
