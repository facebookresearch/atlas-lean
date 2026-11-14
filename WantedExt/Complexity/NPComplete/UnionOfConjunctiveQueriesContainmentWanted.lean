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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.ConjunctiveQueries

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

/-- An instance: the conjunctive queries of `U₁` and of `U₂`, each as its head tuple and its
body atoms `(relation, argument tuple)`. -/
abbrev UnionOfConjunctiveQueriesContainmentInstance :=
  List (List ℕ × List (ℕ × List ℕ)) × List (List ℕ × List (ℕ × List ℕ))

/-- The conjunctive query with head `q.1` and body `q.2`. -/
def toCQ (q : List ℕ × List (ℕ × List ℕ)) : CQ := ⟨q.1, q.2⟩

/-- The conjunctive queries of `U₁`. -/
def union₁ (i : UnionOfConjunctiveQueriesContainmentInstance) : List CQ := i.1.map toCQ

/-- The conjunctive queries of `U₂`. -/
def union₂ (i : UnionOfConjunctiveQueriesContainmentInstance) : List CQ := i.2.map toCQ

/-- Containment of unions of conjunctive queries, at the level of assignments: on every
database `D`, every satisfying assignment `σ` of a conjunctive query `Q` of `U₁` is matched by a
satisfying assignment `τ` of some conjunctive query `Q'` of `U₂` producing the same head tuple.
This reads `U₁(D) ⊆ U₂(D)` for the answer-set semantics. -/
def UnionContained (U₁ U₂ : List CQ) : Prop :=
  ∀ (D : DB) (σ : Assign), ∀ Q ∈ U₁, Satisfies D Q σ →
    ∃ Q' ∈ U₂, ∃ τ : Assign, Satisfies D Q' τ ∧ Q'.head.map τ = Q.head.map σ

/-- Well-formedness of an instance: both unions have at least one conjunctive query, all heads
have the same arity, every relation name occurs with one arity in the atoms of all the queries,
and every head variable of each query occurs in an atom of that query. -/
def WellFormed (i : UnionOfConjunctiveQueriesContainmentInstance) : Prop :=
  union₁ i ≠ [] ∧ union₂ i ≠ [] ∧
    (∀ Q ∈ union₁ i ++ union₂ i, ∀ Q' ∈ union₁ i ++ union₂ i, Q.head.length = Q'.head.length) ∧
    (∀ Q ∈ union₁ i ++ union₂ i, ∀ Q' ∈ union₁ i ++ union₂ i, ∀ a ∈ Q.body, ∀ b ∈ Q'.body,
      a.1 = b.1 → a.2.length = b.2.length) ∧
    ∀ Q ∈ union₁ i ++ union₂ i, ∀ x ∈ Q.head, ∃ a ∈ Q.body, x ∈ a.2

/-- `U₁` is contained in `U₂`. -/
def UnionOfConjunctiveQueriesContainmentFeasible
    (i : UnionOfConjunctiveQueriesContainmentInstance) : Prop :=
  UnionContained (union₁ i) (union₂ i)

open Classical in
/-- UNION OF CONJUNCTIVE QUERIES CONTAINMENT as a decision problem over bitstrings. -/
noncomputable def unionOfConjunctiveQueriesContainmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnionOfConjunctiveQueriesContainmentInstance) x with
  | some i => decide (WellFormed i ∧ UnionOfConjunctiveQueriesContainmentFeasible i)
  | none => false

/-- **UNION OF CONJUNCTIVE QUERIES CONTAINMENT is NP-complete.** Source: Sagiv and Yannakakis
(1980); Abo Khamis, Kolaitis, Ngo and Suciu (2020), Section 1. -/
public theorem_wanted unionOfConjunctiveQueriesContainment_npComplete :
    unionOfConjunctiveQueriesContainmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unionOfConjunctiveQueriesContainmentDec

end MetaMathlibExt.Complexity.NPComplete.UnionOfConjunctiveQueriesContainment
