/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES, `≤` and `>` only, is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO16] CONJUNCTIVE SATISFIABILITY
WITH FUNCTIONS AND INEQUALITIES, comment: remains NP-complete even if `=` and `≠` are not used;
V. R. Pratt, "Two easy theories whose combination is hard", technical report, Massachusetts
Institute of Technology (1977), http://boole.stanford.edu/pub/sefnp.pdf.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityOrderRelationsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityOrderRelations

open MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityFunctionsInequalities

/-!
# CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES, `≤` and `>` only, is NP-complete

Garey and Johnson's problem: a set `U` of variables, a set `F` of univariate function symbols,
and a collection `C` of clauses `U * V` where `*` is `≤` or `>` (the comment's restriction: `=`
and `≠` are not used), and each of `U`, `V` is `0`, `1`, `u`, `f(0)`, `f(1)` or `f(u)` for some
`f ∈ F` and `u ∈ U`. QUESTION: is there an assignment of integer values to the variables and to
the terms `f(u)`, `f(0)`, `f(1)` satisfying every clause under the usual interpretation of `≤`
and `>`?

This is the restriction of `ConjunctiveSatisfiabilityFunctionsInequalitiesWanted` (Pratt's
general term syntax, relations `≤`, `>`, `=`, `≠`) to Garey and Johnson's term shapes and to the
relations `≤` and `>`. Terms are that module's node lists; `WellFormed` adds: every constant is
`0` or `1`, every application has exactly one argument, and that argument is a variable or a
constant node (so terms are `0`, `1`, `u`, `f(0)`, `f(1)`, `f(u)`); every clause relation is `0`
(`≤`) or `1` (`>`). The values of the terms `f(t)` come from a function `φ f` on the integers,
so equal arguments give equal values, as in Pratt's combination of the theories of `≤` and of
uninterpreted functions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES restricted to `≤` and `>` is
NP-complete.** Source: Garey and Johnson (1979), [LO16], comment; Pratt (1977). -/
public theorem_wanted orderRelations_npComplete :
    orderRelationsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L orderRelationsDec

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityOrderRelations
