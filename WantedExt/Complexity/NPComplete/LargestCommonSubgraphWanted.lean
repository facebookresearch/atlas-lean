/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LARGEST COMMON SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT49] LARGEST
COMMON SUBGRAPH (transformation from CLIQUE; no other reference given there).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LargestCommonSubgraph

/-!
# LARGEST COMMON SUBGRAPH is NP-complete

INSTANCE: graphs `G = (V₁, E₁)`, `H = (V₂, E₂)`, and a positive integer `K`.
QUESTION: do there exist subsets `E₁' ⊆ E₁` and `E₂' ⊆ E₂` with `|E₁'| = |E₂'| ≥ K` such that
the two subgraphs `G' = (V₁, E₁')` and `H' = (V₂, E₂')` are isomorphic?

A subset `E₁' ⊆ E₁` is the same thing as a spanning subgraph `G' ≤ G` on `V₁` (Mathlib's
order on `SimpleGraph`), with edge set `E₁'`; likewise for `H`. Isomorphism is Mathlib's
`SimpleGraph.Iso`. As in the source, the subgraphs keep all vertices, so a yes-instance has
`|V₁| = |V₂|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n₁` of `G` (vertices `Fin n₁`), edge list of `G`, vertex count
`n₂` of `H` (vertices `Fin n₂`), edge list of `H`, and the bound `K`. -/
abbrev LargestCommonSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ) × ℕ

/-- The first graph `G = (V₁, E₁)` as a `SimpleGraph (Fin n₁)`. -/
def GraphG (i : LargestCommonSubgraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The second graph `H = (V₂, E₂)` as a `SimpleGraph (Fin n₂)`. -/
def GraphH (i : LargestCommonSubgraphInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2.1

/-- Well-formedness of an instance: both edge lists describe simple graphs (no duplicate edges
in either orientation, no self-loops, endpoints in range), and `K` is positive. -/
def WellFormed (i : LargestCommonSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.2.1.Nodup ∧
      ∀ e ∈ i.2.2.2.1, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2.1) ∧
    0 < i.2.2.2.2

/-- Spanning subgraphs `G' ≤ G` and `H' ≤ H` with the same number of edges, at least `K`, that
are isomorphic. -/
def LargestCommonSubgraphFeasible (i : LargestCommonSubgraphInstance) : Prop :=
  ∃ G' : SimpleGraph (Fin i.1), ∃ H' : SimpleGraph (Fin i.2.2.1),
    G' ≤ GraphG i ∧ H' ≤ GraphH i ∧
      G'.edgeSet.ncard = H'.edgeSet.ncard ∧ i.2.2.2.2 ≤ G'.edgeSet.ncard ∧
        Nonempty (G' ≃g H')

open Classical in
/-- LARGEST COMMON SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def largestCommonSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LargestCommonSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ LargestCommonSubgraphFeasible i)
  | none => false

/-- **LARGEST COMMON SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT49]. -/
public theorem_wanted largestCommonSubgraph_npComplete :
    largestCommonSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L largestCommonSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.LargestCommonSubgraph
