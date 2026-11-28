/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONJUNCTIVE QUERY CONTAINMENT: definitions

Source:
A. K. Chandra and P. M. Merlin, "Optimal implementation of conjunctive queries in relational
data bases", Proceedings of the 9th Annual ACM Symposium on Theory of Computing (STOC 1977),
77-90, doi:10.1145/800105.803397;
S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley (1995),
Theorem 6.2.10(a) (containment of tableau queries is NP-complete, also for single-relation
queries without constants; credited there to Chandra and Merlin).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.ConjunctiveQueries

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConjunctiveQueryContainment

open Cslib.Databases.ConjunctiveQueries

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

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveQueryContainment
