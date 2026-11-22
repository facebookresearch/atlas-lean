/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESILIENCE OF THE TRIANGLE QUERY is NP-complete

Source:
C. Freire, W. Gatterbauer, N. Immerman and A. Meliou, "The complexity of resilience and
responsibility for self-join-free conjunctive queries", Proceedings of the VLDB Endowment 9(3)
(2015), 180-191, doi:10.14778/2850583.2850592, Definition 2 (resilience) and Proposition 10
(`RES(q△)` is NP-complete); extended version arXiv:1507.00674, Definition 2.1 and
Proposition 3.3 (reduction from 3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.ConjunctiveQueries
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangleQueryResilience

open Cslib.Databases.ConjunctiveQueries

/-!
# RESILIENCE OF THE TRIANGLE QUERY is NP-complete

The triangle query is the self-join-free Boolean conjunctive query
`q△ :- R(x, y), S(y, z), T(z, x)`, with every relation endogenous (its tuples may be deleted).
Its resilience problem `RES(q△)`:

INSTANCE: a database `D` with binary relations `R`, `S`, `T`, and an integer `k`.
QUESTION: does `D ⊨ q△` hold, and is there a set `Γ` of at most `k` tuples of `D` such that
`D - Γ ⊭ q△`?

The query and the satisfaction relation are those of `CSLibExt.Databases.ConjunctiveQueries`:
`q△` is the `CQ` with empty head and body `R(x, y), S(y, z), T(z, x)`, the relation names
`R, S, T` being `0, 1, 2` and the variables `x, y, z` being `0, 1, 2`; `D ⊨ q` is the
existence of a satisfying assignment (`Satisfies`). The domain is `ℕ` and a relation is given
by the list of its tuples (pairs), without repetition. Deleting `Γ` leaves a database `D'`
with `D' r ⊆ D r` for every relation `r`, and `|Γ|` is the number of tuples removed,
`∑ r ∈ {R, S, T}, |D r \ D' r|`; conversely every such `D'` arises from `Γ = D \ D'`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The triangle query `q△ :- R(x, y), S(y, z), T(z, x)`, with `R, S, T` named `0, 1, 2` and
`x, y, z` numbered `0, 1, 2`. -/
def triangleQuery : CQ := ⟨[], [(0, [0, 1]), (1, [1, 2]), (2, [2, 0])]⟩

/-- An instance: the tuples of `R`, `S` and `T`, and the bound `k`. -/
abbrev TriangleQueryResilienceInstance :=
  List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The database of the instance: relation `0` is `R`, `1` is `S`, `2` is `T`, and every other
relation is empty. -/
def database (i : TriangleQueryResilienceInstance) : DB := fun r =>
  ((if r = 0 then i.1 else if r = 1 then i.2.1 else if r = 2 then i.2.2.1 else []).map
    fun t => [t.1, t.2]).toFinset

/-- Well-formedness of an instance: no relation lists a tuple twice. -/
def WellFormed (i : TriangleQueryResilienceInstance) : Prop :=
  i.1.Nodup ∧ i.2.1.Nodup ∧ i.2.2.1.Nodup

/-- `(D, k) ∈ RES(q△)`: `D ⊨ q△`, and deleting at most `k` tuples of `D` leaves a database
`D'` with `D' ⊭ q△`. -/
def TriangleQueryResilienceFeasible (i : TriangleQueryResilienceInstance) : Prop :=
  (∃ σ, Satisfies (database i) triangleQuery σ) ∧
    ∃ D' : DB, (∀ r, D' r ⊆ database i r) ∧
      ∑ r ∈ Finset.range 3, (database i r \ D' r).card ≤ i.2.2.2 ∧
      ¬ ∃ σ, Satisfies D' triangleQuery σ

open Classical in
/-- RESILIENCE OF THE TRIANGLE QUERY as a decision problem over bitstrings. -/
noncomputable def triangleQueryResilienceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleQueryResilienceInstance) x with
  | some i => decide (WellFormed i ∧ TriangleQueryResilienceFeasible i)
  | none => false

/-- **RESILIENCE OF THE TRIANGLE QUERY is NP-complete.** Source: Freire, Gatterbauer, Immerman
and Meliou (2015), Proposition 10. -/
public theorem_wanted triangleQueryResilience_npComplete :
    triangleQueryResilienceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L triangleQueryResilienceDec

end MetaMathlibExt.Complexity.NPComplete.TriangleQueryResilience
