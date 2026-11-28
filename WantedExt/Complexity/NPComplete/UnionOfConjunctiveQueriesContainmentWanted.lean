/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNION OF CONJUNCTIVE QUERIES CONTAINMENT is NP-complete

Source:
Y. Sagiv and M. Yannakakis, "Equivalences among relational expressions with the union and
difference operators", Journal of the ACM 27(4) (1980), 633-655, doi:10.1145/322217.322221
(a union of conjunctive queries is contained in another exactly when each of its conjunctive
queries is contained in one of the other's);
M. Abo Khamis, P. G. Kolaitis, H. Q. Ngo and D. Suciu, "Bag query containment and information
theory", Proceedings of the 39th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database
Systems (PODS 2020), 95-112, doi:10.1145/3375395.3387645, arXiv:1906.09727 (Section 1: under set
semantics, containment "is NP-complete for unions of conjunctive queries", credited to Sagiv and
Yannakakis).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnionOfConjunctiveQueriesContainmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnionOfConjunctiveQueriesContainment

open Cslib.Databases.ConjunctiveQueries

/-!
# UNION OF CONJUNCTIVE QUERIES CONTAINMENT is NP-complete

INSTANCE: two unions of conjunctive queries `U₁ = Q₁ ∪ ⋯ ∪ Qₖ` and `U₂ = Q'₁ ∪ ⋯ ∪ Q'ₗ`
(`k, l ≥ 1`) over one relational schema, all heads of the same arity.
QUESTION: is `U₁` contained in `U₂` over all database instances, that is,
`U₁(D) ⊆ U₂(D)` for every database `D`, where `U(D)` is the union of the answers `Q(D)` of the
conjunctive queries `Q` of `U`?

The conjunctive queries are those of `CSLibExt.Databases.ConjunctiveQueries` (`CQ`): a head
tuple of variables and a list of body atoms `(relation, argument tuple)`, with variables and
relation names in `ℕ` and no constants; databases (`DB`) are finite, over the domain `ℕ`.
Containment is read at the level of assignments, as that module's `Contained` reads
`Q(D) ⊆ Q'(D)`: every satisfying assignment of a conjunctive query of `U₁` produces a head tuple
that some conjunctive query of `U₂` produces under some satisfying assignment. "Over one schema"
is the condition that every relation name occurs with one arity in all the queries; every head
variable of a query also occurs in its body (range restriction), as in the existing statement
`WantedExt.Complexity.NPComplete.ConjunctiveQueryContainmentWanted`.

Sagiv and Yannakakis show that `U₁ ⊆ U₂` exactly when each `Qᵢ` is contained in some `Q'ⱼ`,
which with the Chandra-Merlin homomorphism theorem puts the problem in NP; the special case
`k = l = 1` is conjunctive query containment, which is NP-hard.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNION OF CONJUNCTIVE QUERIES CONTAINMENT is NP-complete.** Source: Sagiv and Yannakakis
(1980); Abo Khamis, Kolaitis, Ngo and Suciu (2020), Section 1. -/
public theorem_wanted unionOfConjunctiveQueriesContainment_npComplete :
    unionOfConjunctiveQueriesContainmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unionOfConjunctiveQueriesContainmentDec

end MetaMathlibExt.Complexity.NPComplete.UnionOfConjunctiveQueriesContainment
