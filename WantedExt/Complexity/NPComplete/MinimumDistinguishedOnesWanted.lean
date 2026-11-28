/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM DISTINGUISHED ONES is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM DISTINGUISHED ONES (decision version);
V. Kann, "Polynomially bounded minimization problems which are hard to approximate", Proc.
20th ICALP, LNCS 700 (1993), 52-63, doi:10.1007/3-540-56939-1_61;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (satisfiability with at most three literals per clause is
NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumDistinguishedOnesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumDistinguishedOnes

/-!
# MINIMUM DISTINGUISHED ONES is NP-complete

INSTANCE: disjoint sets `X`, `Z` of variables, a collection `C` of disjunctive clauses of at
most 3 literals over `X ∪ Z` (a literal is a variable or a negated variable), and a bound `K`.
QUESTION: is there a truth assignment for `X` and `Z` that satisfies every clause of `C` and
sets at most `K` variables of `Z` to true?

This is the decision version of the compendium's MINIMUM DISTINGUISHED ONES (measure: the
number of `Z` variables set to true), shown NPO PB-complete by Kann. NP-hardness of the decision
version is immediate: with `Z = ∅` and `K = 0` it asks whether a formula with at most three
literals per clause is satisfiable, which Karp (1972) proved NP-complete.

The variables are `0, …, n - 1`; `Z` is listed (without repetition) and `X` is the rest. The
formula uses the repository's `Cslib.Logic.LegacyPL.CNF` (a clause is a list of literals
`(variable, polarity)`) with its semantics `Cslib.Logic.LegacyPL.CNF.Satisfies`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM DISTINGUISHED ONES is NP-complete.** Source: Crescenzi and Kann, MINIMUM DISTINGUISHED
ONES; Kann (1993); Karp (1972). -/
public theorem_wanted minimumDistinguishedOnes_npComplete :
    minimumDistinguishedOnesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumDistinguishedOnesDec

end MetaMathlibExt.Complexity.NPComplete.MinimumDistinguishedOnes
