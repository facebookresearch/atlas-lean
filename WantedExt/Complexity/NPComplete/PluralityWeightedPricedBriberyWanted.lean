/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLURALITY-WEIGHTED-$BRIBERY is NP-complete

Source:
P. Faliszewski, E. Hemaspaandra and L. A. Hemaspaandra, "How hard is bribery in elections?",
Journal of Artificial Intelligence Research 35 (2009), 485-532, doi:10.1613/jair.2676
(arXiv:cs/0608081), Section 2.2 (the problem plurality-weighted-$bribery, nonunique-winner model)
and Theorem 3.2 (it is NP-complete, even for two candidates).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PluralityWeightedPricedBriberyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PluralityWeightedPricedBribery

/-!
# PLURALITY-WEIGHTED-$BRIBERY is NP-complete

INSTANCE: a set `C` of candidates, a collection `V` of voters specified via their preference
lists `prefs₁, …, prefsₙ`, their nonnegative integer weights `w₁, …, wₙ` and their nonnegative
integer prices `π₁, …, πₙ`, a distinguished candidate `p ∈ C`, and a nonnegative integer `k` (the
budget). QUESTION: is there a set `B ⊆ {1, …, n}` with `∑_{i ∈ B} πᵢ ≤ k` and a way to bribe the
voters in `B` (replace their preference lists by arbitrary ones) such that `p` becomes a plurality
winner?

In weighted plurality a candidate's score is the total weight of the voters who rank it first,
and the winners are the candidates of maximum score (the nonunique-winner model, the source's
default). Candidates are `0, …, m - 1`; each preference list contains every candidate exactly
once, most preferred first; voters are the list positions `Fin n`. Binary encoding of all
numbers (Faliszewski, Hemaspaandra and Hemaspaandra give a pseudo-polynomial algorithm).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLURALITY-WEIGHTED-$BRIBERY is NP-complete.** Source: Faliszewski, Hemaspaandra and
Hemaspaandra (2009), Theorem 3.2. -/
public theorem_wanted pluralityWeightedPricedBribery_npComplete :
    pluralityWeightedPricedBriberyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pluralityWeightedPricedBriberyDec

end MetaMathlibExt.Complexity.NPComplete.PluralityWeightedPricedBribery
