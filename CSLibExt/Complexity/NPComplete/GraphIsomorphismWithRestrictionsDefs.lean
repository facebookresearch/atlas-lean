/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH ISOMORPHISM WITH RESTRICTIONS: definitions

Source:
A. Lubiw, "Some NP-complete problems similar to graph isomorphism", SIAM Journal on Computing
10 (1981), 11-21, doi:10.1137/0210002 (original not available here);
V. Arvind, J. Köbler, S. Kuhnert and J. Torán, "Finding small weight isomorphisms with
additional constraints is fixed-parameter tractable", IPEC 2017, LIPIcs 89 (2018), 2:1-2:13,
doi:10.4230/LIPIcs.IPEC.2017.2 (abstract: the problem statement quoted below, attributed to
Lubiw, "In the non-parameterized setting, all these problems are NP-complete").
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphIsomorphismWithRestrictions

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

end MetaMathlibExt.Complexity.NPComplete.GraphIsomorphismWithRestrictions
