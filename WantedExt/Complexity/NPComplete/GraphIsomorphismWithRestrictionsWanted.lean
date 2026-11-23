/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH ISOMORPHISM WITH RESTRICTIONS is NP-complete

Source:
A. Lubiw, "Some NP-complete problems similar to graph isomorphism", SIAM Journal on Computing
10 (1981), 11-21, doi:10.1137/0210002 (original not available here);
V. Arvind, J. Köbler, S. Kuhnert and J. Torán, "Finding small weight isomorphisms with
additional constraints is fixed-parameter tractable", IPEC 2017, LIPIcs 89 (2018), 2:1-2:13,
doi:10.4230/LIPIcs.IPEC.2017.2 (abstract: the problem statement quoted below, attributed to
Lubiw, "In the non-parameterized setting, all these problems are NP-complete").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphIsomorphismWithRestrictions

/-!
# GRAPH ISOMORPHISM WITH RESTRICTIONS is NP-complete

INSTANCE: graphs `X₁ = (V, E₁)` and `X₂ = (V, E₂)` and a set `R ⊆ V × V` of forbidden pairs.
QUESTION: is there an isomorphism `π` from `X₁` to `X₂` with `π(i) ≠ j` for all `(i, j) ∈ R`?

Arvind, Köbler, Kuhnert and Torán (abstract): "Lubiw showed that several variants of Graph
Isomorphism are NP-complete … One of these, called Isomorphism With Restrictions, is to decide
for two given graphs `X_1 = (V, E_1)` and `X_2 = (V, E_2)` and a subset `R ⊆ V × V` of forbidden
pairs whether there is an isomorphism `π` from `X_1` to `X_2` such that `i^π ≠ j` for all
`(i, j) ∈ R`."

The vertex set is `Fin n`; the two graphs are given by edge lists
(`Cslib.Complexity.Karp.edgeGraph`) and `R` by a list of pairs of vertices (a list with
repetitions describes the same set). An isomorphism is a Mathlib graph isomorphism
`Graph₁ i ≃g Graph₂ i`, and `π(i) ≠ j` for all `(i, j) ∈ R` says that no pair `(v, π v)` lies
in `R`. The vertex count is binary, so a whole permutation of `Fin n` is not a polynomial
certificate; but a vertex named neither in `E₁` nor as the first entry of a pair of `R` is
isolated in `X₁` and unrestricted, so it may be sent to any vertex isolated in `X₂` that is not
already used. A certificate is therefore `π` on the named vertices, checked to be injective,
adjacency-preserving in both directions among them, to avoid `R`, to hit every vertex that is
named in `E₂`, and to send every vertex not named in `E₁` to one not named in `E₂`; membership
in NP holds for this encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge lists `E₁` and `E₂`, and the
list `R` of forbidden pairs. -/
abbrev GraphIsomorphismWithRestrictionsInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- The first graph `X₁` as a `SimpleGraph (Fin n)`. -/
def Graph₁ (i : GraphIsomorphismWithRestrictionsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The second graph `X₂` as a `SimpleGraph (Fin n)`. -/
def Graph₂ (i : GraphIsomorphismWithRestrictionsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.2.1

/-- Well-formedness of an instance: both edge lists describe simple graphs on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and every forbidden
pair is a pair of vertices. -/
def WellFormed (i : GraphIsomorphismWithRestrictionsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.1.Nodup ∧ ∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.1) ∧
    ∀ p ∈ i.2.2.2, p.1 < i.1 ∧ p.2 < i.1

/-- There is an isomorphism from `X₁` to `X₂` that maps no vertex `v` to a vertex `w` with
`(v, w) ∈ R`. -/
def GraphIsomorphismWithRestrictionsFeasible
    (i : GraphIsomorphismWithRestrictionsInstance) : Prop :=
  ∃ π : Graph₁ i ≃g Graph₂ i, ∀ v : Fin i.1, ((v : ℕ), ((π v : Fin i.1) : ℕ)) ∉ i.2.2.2

open Classical in
/-- GRAPH ISOMORPHISM WITH RESTRICTIONS as a decision problem over bitstrings. -/
noncomputable def graphIsomorphismWithRestrictionsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphIsomorphismWithRestrictionsInstance) x with
  | some i => decide (WellFormed i ∧ GraphIsomorphismWithRestrictionsFeasible i)
  | none => false

/-- **GRAPH ISOMORPHISM WITH RESTRICTIONS is NP-complete.** Source: Lubiw (1981). -/
public theorem_wanted graphIsomorphismWithRestrictions_npComplete :
    graphIsomorphismWithRestrictionsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphIsomorphismWithRestrictionsDec

end MetaMathlibExt.Complexity.NPComplete.GraphIsomorphismWithRestrictions
