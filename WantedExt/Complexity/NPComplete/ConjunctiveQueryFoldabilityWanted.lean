/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONJUNCTIVE QUERY FOLDABILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR30] CONJUNCTIVE QUERY
FOLDABILITY, p. 233 (reference [Chandra and Merlin, 1977]; transformation from GRAPH
3-COLORABILITY);
A. K. Chandra and P. M. Merlin, "Optimal implementation of conjunctive queries in relational
data bases", Proceedings of the 9th Annual ACM Symposium on Theory of Computing (STOC 1977),
77-90, doi:10.1145/800105.803397.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Dedup

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConjunctiveQueryFoldability

/-!
# CONJUNCTIVE QUERY FOLDABILITY is NP-complete

INSTANCE: a finite domain set `D`, a collection `R = {R₁, R₂, …, Rₘ}` of relations, where each
`Rᵢ` consists of a set of `dᵢ`-tuples with entries from `D`, a set `X` of distinguished
variables, a set `Y` of undistinguished variables, and two "queries" `Q₁` and `Q₂` over `X`,
`Y`, `D`, and `R`, where a query `Q` has the form
`(x₁, x₂, …, x_k)(∃ y₁, y₂, …, y_l)(A₁ ∧ A₂ ∧ ⋯ ∧ A_r)` for some `k`, `l`, and `r`, with
`X' = {x₁, x₂, …, x_k} ⊆ X`, `Y' = {y₁, y₂, …, y_l} ⊆ Y`, and each `Aᵢ` of the form
`Rⱼ(u₁, u₂, …, u_{dⱼ})` with each `u ∈ D ∪ X' ∪ Y'`.
QUESTION: is there a function `σ : Y → X ∪ Y ∪ D` such that, if for each `y ∈ Y` the symbol
`σ(y)` is substituted for every occurrence of `y` in `Q₁`, then the result is query `Q₂`?

The domain is `D = {0, …, |D| - 1}`, the variables are `x₀, …, x_{|X|-1}` and
`y₀, …, y_{|Y|-1}`, and a symbol of `D ∪ X ∪ Y` is a term: `(0, c)` is the element `c`,
`(1, k)` is `xₖ` and `(2, k)` is `yₖ`. A relation is its arity `d` and the list of its tuples.
A query is its tuple `(x₁, …, x_k)` of distinguished variables (as indices) and the list of
its atoms `(j, [u₁, …, u_d])`, read `Rⱼ(u₁, …, u_d)` with relations indexed from `0`.

Two readings are fixed here. The quantifier prefix `(∃ y₁, …, y_l)` binds the undistinguished
variables of the query, so it is determined by the atoms and is not stored (a quantifier over
a variable that occurs in no atom is vacuous); after the substitution, the result's prefix
binds the undistinguished variables that remain. The conjunction `A₁ ∧ ⋯ ∧ A_r` is compared as
the set of its atoms (conjunction is commutative and idempotent): read as sequences, the
substitution would have to map the `i`-th atom of `Q₁` to the `i`-th atom of `Q₂`, which
determines `σ` position by position and makes the problem polynomial, whereas the source's
transformation from GRAPH 3-COLORABILITY folds many atoms onto few.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A conjunctive query: its tuple of distinguished variables and its atoms. -/
abbrev ConjunctiveQuery := List ℕ × List (ℕ × List (ℕ × ℕ))

/-- An instance: `|D|`, the relations (arity, tuples), `|X|`, `|Y|`, and the queries `Q₁`,
`Q₂`. -/
abbrev ConjunctiveQueryFoldabilityInstance :=
  ℕ × List (ℕ × List (List ℕ)) × ℕ × ℕ × ConjunctiveQuery × ConjunctiveQuery

/-- `t` is a symbol of `D ∪ X ∪ Y` (with `|D| = nD`, `|X| = nX`, `|Y| = nY`). -/
def IsTerm (nD nX nY : ℕ) (t : ℕ × ℕ) : Prop :=
  (t.1 = 0 ∧ t.2 < nD) ∨ (t.1 = 1 ∧ t.2 < nX) ∨ (t.1 = 2 ∧ t.2 < nY)

/-- `Q` is a query over `X`, `Y`, `D` and `R`: its distinguished variables lie in `X`, and
each atom `Rⱼ(u₁, …, u_d)` names a relation of `R`, has that relation's arity, and has
arguments in `D ∪ X' ∪ Y`, with `X'` the query's distinguished variables. -/
def IsQuery (nD : ℕ) (R : List (ℕ × List (List ℕ))) (nX nY : ℕ) (Q : ConjunctiveQuery) :
    Prop :=
  (∀ k ∈ Q.1, k < nX) ∧
    ∀ a ∈ Q.2, a.1 < R.length ∧ a.2.length = (R.getD a.1 (0, [])).1 ∧
      ∀ u ∈ a.2, IsTerm nD nX nY u ∧ (u.1 = 1 → u.2 ∈ Q.1)

/-- Well-formedness of an instance: every tuple of a relation has its relation's arity and
entries in `D`, and both queries are queries over `X`, `Y`, `D` and `R`. -/
def WellFormed (i : ConjunctiveQueryFoldabilityInstance) : Prop :=
  (∀ r ∈ i.2.1, ∀ t ∈ r.2, t.length = r.1 ∧ ∀ c ∈ t, c < i.1) ∧
    IsQuery i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 ∧
    IsQuery i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.2

/-- Substitute `σ(yₖ)` for every occurrence of each undistinguished variable `yₖ`. -/
def subst (σ : ℕ → ℕ × ℕ) (u : ℕ × ℕ) : ℕ × ℕ :=
  if u.1 = 2 then σ u.2 else u

/-- Some `σ : Y → X ∪ Y ∪ D` turns `Q₁` into `Q₂`: the distinguished tuples agree (the
substitution does not touch them) and the substituted atoms of `Q₁` form the set of atoms of
`Q₂`. -/
def ConjunctiveQueryFoldabilityFeasible (i : ConjunctiveQueryFoldabilityInstance) : Prop :=
  ∃ σ : ℕ → ℕ × ℕ, (∀ k < i.2.2.2.1, IsTerm i.1 i.2.2.1 i.2.2.2.1 (σ k)) ∧
    i.2.2.2.2.1.1 = i.2.2.2.2.2.1 ∧
    (i.2.2.2.2.1.2.map fun a => (a.1, a.2.map (subst σ))).toFinset = i.2.2.2.2.2.2.toFinset

open Classical in
/-- CONJUNCTIVE QUERY FOLDABILITY as a decision problem over bitstrings. -/
noncomputable def conjunctiveQueryFoldabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConjunctiveQueryFoldabilityInstance) x with
  | some i => decide (WellFormed i ∧ ConjunctiveQueryFoldabilityFeasible i)
  | none => false

/-- **CONJUNCTIVE QUERY FOLDABILITY is NP-complete.** Source: Garey and Johnson (1979),
[SR30]; Chandra and Merlin (1977). -/
public theorem_wanted conjunctiveQueryFoldability_npComplete :
    conjunctiveQueryFoldabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L conjunctiveQueryFoldabilityDec

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveQueryFoldability
