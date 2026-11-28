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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConjunctiveQueryFoldabilityDefs

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

/-- **CONJUNCTIVE QUERY FOLDABILITY is NP-complete.** Source: Garey and Johnson (1979),
[SR30]; Chandra and Merlin (1977). -/
public theorem_wanted conjunctiveQueryFoldability_npComplete :
    conjunctiveQueryFoldabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L conjunctiveQueryFoldabilityDec

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveQueryFoldability
