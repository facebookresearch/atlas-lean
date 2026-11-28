/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO16] CONJUNCTIVE SATISFIABILITY
WITH FUNCTIONS AND INEQUALITIES;
V. R. Pratt, "Two easy theories whose combination is hard", technical report, Massachusetts
Institute of Technology (1977), http://boole.stanford.edu/pub/sefnp.pdf.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityFunctionsInequalitiesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityFunctionsInequalities

/-!
# CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES is NP-complete

Given a conjunction of literals `t₁ R t₂` with `R ∈ {≤, >, =, ≠}`, where the terms `t₁, t₂` are
built from variables, integer constants and uninterpreted function symbols, is there an
assignment of integers to the variables and of functions on the integers to the function
symbols that satisfies every literal? Here `≤` and the integer constants have their standard
meaning on `ℤ`, and `>`, `≠` are the negations of `≤`, `=` (Pratt's "literals (possibly
negated atomic formulae)").

Terms are given as a list of nodes, each node one term occurrence:

* `(0, (x, 0), [])` is the variable number `x`;
* `(1, (p, q), [])` is the integer constant `p - q`;
* `(2, (f, 0), [j₁, …, jₖ])` is the function symbol number `f` applied to the terms at the
  earlier nodes `j₁, …, jₖ`.

A literal `(r, l, l')` relates the terms at nodes `l` and `l'` by `≤`, `>`, `=` or `≠` for
`r = 0, 1, 2, 3`. `WellFormed` requires every node to be used at most once (as an argument or a
literal side), so the nodes form a forest of term trees, the usual syntax of terms, and each
function symbol to have one arity. A function symbol `f` of arity `k` is interpreted by
`φ f : List ℤ → ℤ` on lists of length `k`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES is NP-complete.** Source: Garey
and Johnson (1979), [LO16]; Pratt (1977). -/
public theorem_wanted conjunctiveSatisfiability_npComplete :
    conjunctiveSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L conjunctiveSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityFunctionsInequalities
