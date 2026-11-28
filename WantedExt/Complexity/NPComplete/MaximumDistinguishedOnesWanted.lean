/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM DISTINGUISHED ONES is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM DISTINGUISHED ONES;
V. Kann, *On the Approximability of NP-complete Optimization Problems*, PhD thesis, Royal
Institute of Technology, Stockholm (1992), problem [7.13] Max distinguished ones;
A. Panconesi and D. Ranjan, "Quantifiers and approximation", Theoretical Computer Science 107
(1993), 145-163, doi:10.1016/0304-3975(93)90259-V;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO2] 3-SATISFIABILITY (the special case described
below), from S. A. Cook, "The complexity of theorem-proving procedures", Proc. 3rd Annual ACM
Symposium on Theory of Computing (1971), 151-158, doi:10.1145/800157.805047.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumDistinguishedOnesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumDistinguishedOnes

/-!
# MAXIMUM DISTINGUISHED ONES is NP-complete

INSTANCE: disjoint sets `X`, `Z` of variables, a collection `C` of disjunctive clauses of at
most 3 literals over `X ∪ Z`, and a positive integer `K`. QUESTION: is there a truth assignment
for `X` and `Z` that satisfies every clause of `C` and sets at least `K` variables of `Z` to
true?

This is the decision version of MAXIMUM DISTINGUISHED ONES in the compendium of Crescenzi and
Kann (Kann's Max Dones), whose measure is the number of variables of `Z` set to true. When `Z`
is a single variable that occurs in no clause and `K = 1`, the question is whether `C` is
satisfiable, i.e. 3-SATISFIABILITY with clauses of at most three literals.

The variables are `0, …, |X| + |Z| - 1`: `X` is `0, …, |X| - 1` and `Z` is
`|X|, …, |X| + |Z| - 1`. The clauses are a `Cslib.Logic.LegacyPL.CNF` (a literal is a variable with
its polarity), each with at most three literals over these variables, and an assignment is a
list of `|X| + |Z|` truth values.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM DISTINGUISHED ONES is NP-complete.** Source: Crescenzi and Kann, MAXIMUM
DISTINGUISHED ONES; Kann (1992), [7.13]. -/
public theorem_wanted maximumDistinguishedOnes_npComplete :
    maximumDistinguishedOnesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumDistinguishedOnesDec

end MetaMathlibExt.Complexity.NPComplete.MaximumDistinguishedOnes
