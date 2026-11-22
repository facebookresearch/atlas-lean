/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONJUNCTIVE QUERY CONTAINMENT is NP-complete

Source:
A. K. Chandra and P. M. Merlin, "Optimal implementation of conjunctive queries in relational
data bases", Proceedings of the 9th Annual ACM Symposium on Theory of Computing (STOC 1977),
77-90, doi:10.1145/800105.803397;
S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley (1995),
Theorem 6.2.10(a) (containment of tableau queries is NP-complete, also for single-relation
queries without constants; credited there to Chandra and Merlin).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.ConjunctiveQueries

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConjunctiveQueryContainment

open Cslib.Databases.ConjunctiveQueries

/-!
# CONJUNCTIVE QUERY CONTAINMENT is NP-complete

INSTANCE: two conjunctive queries `Q₁ = ans(u₁) ← R₁(v₁), …, Rₘ(vₘ)` and
`Q₂ = ans(u₂) ← S₁(w₁), …, Sₙ(wₙ)` over one relational schema, with heads of the same arity.
QUESTION: is `Q₁` contained in `Q₂`, that is, `Q₁(D) ⊆ Q₂(D)` for every database `D`?

The queries are those of `CSLibExt.Databases.ConjunctiveQueries` (`CQ`): a head tuple of
variables and a list of body atoms `(relation, argument tuple)`, with variables and relation
names in `ℕ` and no constants. Containment is that module's `Contained`, its assignment-level
reading of `Q₁(D) ⊆ Q₂(D)` over all databases (`contained_iff_hom` there is the Chandra-Merlin
homomorphism theorem). "Over one schema" is the condition that every relation name occurs with
one arity in both queries; as in Abiteboul, Hull and Vianu, every head variable of a query
also occurs in its body (range restriction).

Constants are not part of this fragment. Abiteboul, Hull and Vianu state that the
NP-completeness of containment remains true for single-relation tableau queries without
constants, which lie in this fragment.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the queries `Q₁` and `Q₂`, each as its head tuple and its body atoms
`(relation, argument tuple)`. -/
abbrev ConjunctiveQueryContainmentInstance :=
  (List ℕ × List (ℕ × List ℕ)) × (List ℕ × List (ℕ × List ℕ))

/-- The query `Q₁` of the instance. -/
def query₁ (i : ConjunctiveQueryContainmentInstance) : CQ := ⟨i.1.1, i.1.2⟩

/-- The query `Q₂` of the instance. -/
def query₂ (i : ConjunctiveQueryContainmentInstance) : CQ := ⟨i.2.1, i.2.2⟩

/-- Well-formedness of an instance: the heads have the same arity, every relation name occurs
with one arity in the atoms of both queries, and every head variable of each query occurs in
an atom of that query. -/
def WellFormed (i : ConjunctiveQueryContainmentInstance) : Prop :=
  (query₁ i).head.length = (query₂ i).head.length ∧
    (∀ a ∈ (query₁ i).body ++ (query₂ i).body, ∀ b ∈ (query₁ i).body ++ (query₂ i).body,
      a.1 = b.1 → a.2.length = b.2.length) ∧
    (∀ x ∈ (query₁ i).head, ∃ a ∈ (query₁ i).body, x ∈ a.2) ∧
    ∀ x ∈ (query₂ i).head, ∃ a ∈ (query₂ i).body, x ∈ a.2

/-- `Q₁` is contained in `Q₂`. -/
def ConjunctiveQueryContainmentFeasible (i : ConjunctiveQueryContainmentInstance) : Prop :=
  Contained (query₁ i) (query₂ i)

open Classical in
/-- CONJUNCTIVE QUERY CONTAINMENT as a decision problem over bitstrings. -/
noncomputable def conjunctiveQueryContainmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConjunctiveQueryContainmentInstance) x with
  | some i => decide (WellFormed i ∧ ConjunctiveQueryContainmentFeasible i)
  | none => false

/-- **CONJUNCTIVE QUERY CONTAINMENT is NP-complete.** Source: Chandra and Merlin (1977);
Abiteboul, Hull and Vianu (1995), Theorem 6.2.10(a). -/
public theorem_wanted conjunctiveQueryContainment_npComplete :
    conjunctiveQueryContainmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L conjunctiveQueryContainmentDec

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveQueryContainment
