/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED SATISFIABILITY, FIXED NON-SCHAEFER RELATIONS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO6] GENERALIZED
SATISFIABILITY (comment: for any fixed sequence `S` the problem is NP-complete
unless one of six alternatives holds);
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the
Tenth Annual ACM Symposium on Theory of Computing (STOC 1978), 216-226,
doi:10.1145/800133.804350.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneralizedSatisfiabilityFixedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityFixed

open Cslib.Logic.LegacyPL Matrix

/-!
# GENERALIZED SATISFIABILITY, FIXED NON-SCHAEFER RELATIONS is NP-complete

GENERALIZED SATISFIABILITY
(`MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiability`) with the sequence
`S = ⟨R₁, ..., Rₘ⟩` of relations `Rᵢ ⊆ {T, F}^{kᵢ}` fixed. INSTANCE: a set `U` of variables
and, for `1 ≤ i ≤ m`, a collection `Cᵢ` of `kᵢ`-tuples of variables from `U`. QUESTION: is
there a truth assignment `t : U → {T, F}` such that for all `i` and all
`(u[1], ..., u[kᵢ]) ∈ Cᵢ`, `(t(u[1]), ..., t(u[kᵢ])) ∈ Rᵢ`?

Schaefer's dichotomy, as recorded by Garey and Johnson: for any fixed sequence `S`, the
problem is NP-complete unless one of the following six alternatives holds, in which case it
is solvable in polynomial time: (1) each `Rᵢ` contains `{T}^{kᵢ}`, (2) each `Rᵢ` contains
`{F}^{kᵢ}`, (3) each `Rᵢ` is logically "equivalent" to some conjunctive normal form expression
having at most one negated literal per clause, (4) each `Rᵢ` is logically "equivalent" to
some conjunctive normal form expression having at most one un-negated literal per clause,
(5) each `Rᵢ` is logically "equivalent" to some conjunctive normal form expression having at
most 2 literals per clause, or (6) each `Rᵢ` is the "solution set" for some system of linear
equations over `GF[2]`. This module states the NP-complete half: for every fixed sequence `S`
of nonempty relations for which none of (1)-(6) holds, the problem is NP-complete. Schaefer
applies the six-way test to nonempty relations (the nonemptiness condition of his Lemma 4.3).
With an empty relation allowed, the statement would imply P = NP: for the empty unary relation
and the ternary relation `{FFF, FTT, TFT}` none of (1)-(6) holds, yet every instance that uses
the empty relation is unsatisfiable and every other instance is satisfied by the all-false
assignment, so the problem over that sequence is solvable in polynomial time.

A relation is given as in GENERALIZED SATISFIABILITY, by its arity `k` and the list of its tuples
(`true` for `T`). Its coordinates are the variables `0, ..., k - 1`: a CNF expression (ATLAS's CNF
encoding `Cslib.Logic.LegacyPL.CNF`, literals `(variable, polarity)`, polarity `false` for a negated
literal) or a linear system is equivalent to the relation when it uses only these variables and its
models are exactly the tuples of the relation. The instance carries the number `n` of variables and
the collections `C₁, ..., Cₘ`; it is turned into a GENERALIZED SATISFIABILITY instance by pairing
`Cᵢ` with `Rᵢ`, and the well-formedness and question of that module are reused unchanged.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED SATISFIABILITY, FIXED NON-SCHAEFER RELATIONS is NP-complete.** For every
fixed well-formed sequence `S` of nonempty relations satisfying none of Schaefer's six
alternatives, GENERALIZED SATISFIABILITY over `S` is NP-complete. Source: Garey and Johnson
(1979), [LO6]; Schaefer (1978), Theorem 2.1 and the nonemptiness condition of Lemma 4.3. -/
public theorem_wanted generalizedSatisfiabilityFixed_npComplete (S : List Relation)
    (_hS : RelationsWellFormed S) (_hNonempty : ∀ r ∈ S, r.2 ≠ [])
    (_hSchaefer : ¬ SchaeferCondition S) :
    generalizedSatisfiabilityFixedDec S ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (generalizedSatisfiabilityFixedDec S)

end MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityFixed
