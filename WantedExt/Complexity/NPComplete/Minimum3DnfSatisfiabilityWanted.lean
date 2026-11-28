/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM 3DNF SATISFIABILITY is NP-complete

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems* (2000), problem
MINIMUM 3DNF SATISFIABILITY ("Instance: Set U of variables, collection C of conjunctive clauses
of at most three literals ... Measure: Number of clauses satisfied by the truth assignment"),
which the compendium relates to Garey and Johnson's [LO8];
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO8] NON-TAUTOLOGY, comment: remains
NP-complete for expressions in disjunctive normal form with three literals per disjunct
(the case "no clause satisfied" of this problem);
S. A. Cook, "The complexity of theorem-proving procedures", Proceedings of the 3rd Annual ACM
Symposium on Theory of Computing (1971), 151-158, doi:10.1145/800157.805047.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.Minimum3DnfSatisfiabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Minimum3DnfSatisfiability

/-!
# MINIMUM 3DNF SATISFIABILITY is NP-complete

INSTANCE: a set `U` of variables, a collection `C` of conjunctive clauses of at most three
literals over `U` (a literal is a variable or a negated variable), and a positive integer `K`.
QUESTION: is there a truth assignment for `U` that satisfies at most `K` clauses of `C`?

This is the decision version of the compendium's MINIMUM 3DNF SATISFIABILITY. A conjunctive
clause is satisfied when all its literals hold, as a disjunct of a DNF expression in
`MetaMathlibExt.Complexity.KeyTheorems.KarpLuby.dnfSat` (used by `NonTautology3DnfWanted`); the
encoding is that module's: `U = {u₀, …, u_{n-1}}`, a clause is a list of literals `(x, b)` (`uₓ`
if `b = true`, `¬uₓ` if `b = false`), assignments are functions `ℕ → Bool` (only their values on
`0, …, n - 1` matter), and `C` is listed with multiplicity.

Hardness: NON-TAUTOLOGY OF 3DNF ([LO8], comment) asks for an assignment satisfying no clause of
a 3DNF expression; adding the two clauses `u_n` and `¬u_n` over a fresh variable (exactly one of
them holds under every assignment) and taking `K = 1` reduces it to this problem. Membership in
NP: an assignment is a certificate. Negating every clause turns the question into whether some
assignment satisfies at least `|C| - K` disjunctive clauses of at most three literals (MAXIMUM
3-SATISFIABILITY).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM 3DNF SATISFIABILITY is NP-complete.** Source: Crescenzi and Kann, MINIMUM 3DNF
SATISFIABILITY; Garey and Johnson (1979), [LO8] (the case of no satisfied clause); Cook (1971). -/
public theorem_wanted minimum3DnfSatisfiability_npComplete :
    minimum3DnfSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimum3DnfSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.Minimum3DnfSatisfiability
