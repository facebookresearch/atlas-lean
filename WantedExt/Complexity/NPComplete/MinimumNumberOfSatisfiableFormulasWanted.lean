/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM NUMBER OF SATISFIABLE FORMULAS is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM NUMBER OF SATISFIABLE FORMULAS (decision version);
V. Kann, "Polynomially bounded minimization problems which are hard to approximate", Proc.
20th ICALP, LNCS 700 (1993), 52-63, doi:10.1007/3-540-56939-1_61;
R. Kohli, R. Krishnamurti, and P. Mirchandani, "The minimum satisfiability problem", SIAM
Journal on Discrete Mathematics 7 (1994), 275-283, doi:10.1137/S0895480191220836.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumNumberOfSatisfiableFormulasDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumNumberOfSatisfiableFormulas

/-!
# MINIMUM NUMBER OF SATISFIABLE FORMULAS is NP-complete

INSTANCE: a set `U` of variables, a collection `C` of 3CNF formulas over `U`, and a bound
`K`. QUESTION: is there a truth assignment for `U` that satisfies at most `K` formulas of `C`?

This is the decision version of the compendium's MINIMUM NUMBER OF SATISFIABLE FORMULAS
(measure: the number of formulas satisfied), shown NPO PB-complete by Kann through a
transformation from MINIMUM DISTINGUISHED ONES. NP-hardness of the decision version also follows
from the case in which every formula is a single clause: that is MINIMUM SATISFIABILITY, which
Kohli, Krishnamurti, and Mirchandani (1994) prove strongly NP-hard already for clauses of at
most two literals.

A 3CNF formula is a conjunction of clauses of at most three literals each. The variables are
`0, …, n - 1`; formulas use the repository's `Cslib.Logic.LegacyPL.CNF` (a clause is a list of
literals `(variable, polarity)`) with its semantics `Cslib.Logic.LegacyPL.CNF.Satisfies`. The
formulas form a list, so a formula listed twice counts twice.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM NUMBER OF SATISFIABLE FORMULAS is NP-complete.** Source: Crescenzi and Kann,
MINIMUM NUMBER OF SATISFIABLE FORMULAS; Kann (1993); Kohli, Krishnamurti, and Mirchandani (1994). -/
public theorem_wanted minimumNumberOfSatisfiableFormulas_npComplete :
    minimumNumberOfSatisfiableFormulasDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumNumberOfSatisfiableFormulasDec

end MetaMathlibExt.Complexity.NPComplete.MinimumNumberOfSatisfiableFormulas
