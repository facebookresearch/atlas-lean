/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONJUNCTIVE BOOLEAN QUERY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR31] CONJUNCTIVE BOOLEAN QUERY,
p. 233 (reference [Chandra and Merlin, 1977]; transformation from CLIQUE);
A. K. Chandra and P. M. Merlin, "Optimal implementation of conjunctive queries in relational
data bases", Proceedings of the 9th Annual ACM Symposium on Theory of Computing (STOC 1977),
77-90, doi:10.1145/800105.803397.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConjunctiveBooleanQuery

/-!
# CONJUNCTIVE BOOLEAN QUERY is NP-complete

INSTANCE: a finite domain set `D`, a collection `R = {R₁, R₂, …, Rₘ}` of relations, where each
`Rᵢ` consists of a set of `dᵢ`-tuples with entries from `D`, and a conjunctive Boolean query
`Q` over `R` and `D`, where such a query `Q` is of the form
`(∃ y₁, y₂, …, y_l)(A₁ ∧ A₂ ∧ ⋯ ∧ A_r)` with each `Aᵢ` of the form `Rⱼ(u₁, u₂, …, u_{dⱼ})`
where each `u ∈ {y₁, y₂, …, y_l} ∪ D`.
QUESTION: is `Q`, when interpreted as a statement about `R` and `D`, true?

The domain is `D = {0, …, |D| - 1}`. A relation is its arity `d` and the list of its tuples
(lists of length `d`). The query is the number `l` of variables and the list of its atoms
`(j, [u₁, …, u_d])`, read `Rⱼ(u₁, …, u_d)` with relations indexed from `0`; a term `(true, v)`
is the variable `y_v` (indexed from `0`) and `(false, c)` is the domain element `c`. `Q` is true
iff some assignment of domain elements to the variables puts the tuple of every atom into its
relation.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: `|D|`, the relations (arity, tuples), the number `l` of variables, and the
atoms of the query (relation index, argument terms). -/
abbrev ConjunctiveBooleanQueryInstance :=
  ℕ × List (ℕ × List (List ℕ)) × ℕ × List (ℕ × List (Bool × ℕ))

/-- The value of a term under the assignment `σ` of domain elements to the variables:
`σ v` for the variable `y_v`, and `c` for the domain element `c`. -/
def termValue (σ : ℕ → ℕ) (u : Bool × ℕ) : ℕ :=
  if u.1 then σ u.2 else u.2

/-- Well-formedness of an instance: every tuple of a relation has its relation's arity and
entries in `D`; every atom names a relation, has as many arguments as that relation's arity,
and uses only domain elements of `D` and variables `y₀, …, y_{l-1}`. -/
def WellFormed (i : ConjunctiveBooleanQueryInstance) : Prop :=
  (∀ r ∈ i.2.1, ∀ t ∈ r.2, t.length = r.1 ∧ ∀ c ∈ t, c < i.1) ∧
    ∀ a ∈ i.2.2.2, a.1 < i.2.1.length ∧ a.2.length = (i.2.1.getD a.1 (0, [])).1 ∧
      ∀ u ∈ a.2, (u.1 = true → u.2 < i.2.2.1) ∧ (u.1 = false → u.2 < i.1)

/-- The query is true: some assignment of elements of `D` to `y₀, …, y_{l-1}` puts the
argument tuple of every atom into its relation. -/
def ConjunctiveBooleanQueryFeasible (i : ConjunctiveBooleanQueryInstance) : Prop :=
  ∃ σ : ℕ → ℕ, (∀ v < i.2.2.1, σ v < i.1) ∧
    ∀ a ∈ i.2.2.2, a.2.map (termValue σ) ∈ (i.2.1.getD a.1 (0, [])).2

open Classical in
/-- CONJUNCTIVE BOOLEAN QUERY as a decision problem over bitstrings. -/
noncomputable def conjunctiveBooleanQueryDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConjunctiveBooleanQueryInstance) x with
  | some i => decide (WellFormed i ∧ ConjunctiveBooleanQueryFeasible i)
  | none => false

/-- **CONJUNCTIVE BOOLEAN QUERY is NP-complete.** Source: Garey and Johnson (1979), [SR31];
Chandra and Merlin (1977). -/
public theorem_wanted conjunctiveBooleanQuery_npComplete :
    conjunctiveBooleanQueryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L conjunctiveBooleanQueryDec

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveBooleanQuery
