/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNION OF CONJUNCTIVE QUERIES CONTAINMENT: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.ConjunctiveQueries

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnionOfConjunctiveQueriesContainment

open Cslib.Databases.ConjunctiveQueries

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

end MetaMathlibExt.Complexity.NPComplete.UnionOfConjunctiveQueriesContainment
