/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNWEIGHTED COALITIONAL MANIPULATION under Borda with two manipulators is NP-complete

Source:
N. Betzler, R. Niedermeier and G. J. Woeginger, "Unweighted coalitional manipulation under the
Borda rule is NP-hard", Proceedings of the 22nd International Joint Conference on Artificial
Intelligence (IJCAI 2011), 55-60, doi:10.5591/978-1-57735-516-8/IJCAI11-021 (Section 2,
definition of BORDA MANIPULATION; Theorem 3.1);
J. Davies, G. Katsirelos, N. Narodytska and T. Walsh, "Complexity of and algorithms for Borda
manipulation", Proceedings of the 25th AAAI Conference on Artificial Intelligence (AAAI 2011),
657-662, doi:10.1609/aaai.v25i1.7873.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BordaManipulationTwoManipulatorsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BordaManipulationTwoManipulators

/-!
# UNWEIGHTED COALITIONAL MANIPULATION under Borda with two manipulators is NP-complete

INSTANCE: an election `(V, C)`, consisting of a set `C` of candidates and a multiset `V` of
(nonmanipulative) votes, each a linear order on `C`, and a distinguished candidate `c ∈ C`.
QUESTION: is there a multiset `W` (the coalition) of `t = 2` votes over `C` such that `c` is a
Borda winner of `(V ∪ W, C)`?

Under the Borda rule with `m = |C|` candidates, the candidate at position `i` (`1 ≤ i ≤ m`) of a
vote receives `m - i` points from it, and each candidate with the highest total score is a
Borda winner (co-winner model, as in Betzler, Niedermeier and Woeginger). Votes are unweighted.

The candidates are `0, …, m - 1`, and a vote is a list of them in order of preference (a
permutation of `[0, …, m - 1]`, most preferred first). Scores reuse the positional-scoring
`points` and `score` of `WantedExt.Complexity.NPComplete.CoalitionalManipulationBordaWanted`,
with the Borda vector `(m - 1, m - 2, …, 0)` and every vote of weight `1`.

Betzler, Niedermeier and Woeginger prove NP-completeness already for three nonmanipulative
votes and two manipulators (Theorem 3.1); Davies, Katsirelos, Narodytska and Walsh prove
NP-hardness for two manipulators independently. Here the number of nonmanipulative votes is
arbitrary and the number of manipulators is fixed to two.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda (score)

/-- **UNWEIGHTED COALITIONAL MANIPULATION under Borda with two manipulators is NP-complete.**
Source: Betzler, Niedermeier and Woeginger (2011), Theorem 3.1; Davies, Katsirelos, Narodytska
and Walsh (2011). -/
public theorem_wanted bordaManipulation_npComplete :
    bordaManipulationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bordaManipulationDec

end MetaMathlibExt.Complexity.NPComplete.BordaManipulationTwoManipulators
