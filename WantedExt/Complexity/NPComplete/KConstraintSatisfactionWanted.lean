/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-CONSTRAINT SATISFACTION is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MAXIMUM K-CONSTRAINT SATISFACTION (APX-complete; transformation from
MAXIMUM 2-SATISFIABILITY);
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1
(MAXIMUM 2-SATISFIABILITY is NP-complete); M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO5]
MAX 2-SATISFIABILITY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KConstraintSatisfactionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KConstraintSatisfaction

/-!
# K-CONSTRAINT SATISFACTION is NP-complete

For a constant `k ≥ 2`:
INSTANCE: a set `U` of variables, a collection `C` of conjunctive clauses of at most `k`
literals, where a literal is a variable or a negated variable in `U`, and a positive integer
`K`.
QUESTION: is there a truth assignment for `U` that satisfies at least `K` clauses of `C`?

A conjunctive clause is satisfied when all of its literals are true. Variables are
`u₀, ..., u_{n-1}`; a literal is a pair `(j, b)` that is true when `u_j` has the value `b`
(the literal format of `Cslib.Logic.LegacyPL.CNF`), and the clauses are counted with multiplicity by
`Minimum3DnfSatisfiability.satisfiedCount`. The family is stated for each fixed `k ≥ 2`. The
compendium's transformation from MAXIMUM 2-SATISFIABILITY replaces a clause `a ∨ b` by the
three conjunctions `a ∧ b`, `a ∧ ¬b`, `¬a ∧ b`, exactly one of which holds when `a ∨ b` holds
and none otherwise.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **K-CONSTRAINT SATISFACTION is NP-complete for every constant `k ≥ 2`.** Source:
Crescenzi and Kann, MAXIMUM K-CONSTRAINT SATISFACTION; Garey, Johnson and Stockmeyer (1976). -/
public theorem_wanted kConstraintSatisfaction_npComplete (k : ℕ) (hk : 2 ≤ k) :
    kConstraintSatisfactionDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (kConstraintSatisfactionDec k)

end MetaMathlibExt.Complexity.NPComplete.KConstraintSatisfaction
