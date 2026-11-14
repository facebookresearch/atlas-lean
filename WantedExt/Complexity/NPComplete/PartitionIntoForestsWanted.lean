/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO FORESTS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT14] PARTITION INTO
FORESTS (unpublished result; NP-complete already for `K = 2`);
S. L. Hakimi and E. F. Schmeichel, "A note on the vertex arboricity of a
graph", SIAM Journal on Discrete Mathematics 2 (1989), 64-67,
doi:10.1137/0402007 (NP-complete for `K = 2` already on planar graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoForests

/-!
# PARTITION INTO FORESTS is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: can `V` be
partitioned into `k ≤ K` disjoint sets `V₁, ..., Vₖ` such that, for each `i`, the subgraph
induced by `Vᵢ` contains no circuits (is a forest)? This is the question whether the vertex
arboricity of `G` is at most `K`.

The partition is a block map `c : Fin n → Fin k`, block `j` being `{v | c v = j}`; empty blocks
are harmless because the bound is `k ≤ K`. "Induced subgraph" is Mathlib's `SimpleGraph.induce`
and "contains no circuits" is Mathlib's `SimpleGraph.IsAcyclic`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev PartitionIntoForestsInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PartitionIntoForestsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K ≤ |V|`. -/
def WellFormed (i : PartitionIntoForestsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- The vertices split into at most `K` sets, each inducing an acyclic subgraph: for some
`k ≤ K` there is a block map `c : Fin n → Fin k` such that every block `{v | c v = j}` induces
a forest. -/
def PartitionIntoForestsFeasible (i : PartitionIntoForestsInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ c : Fin i.1 → Fin k,
    ∀ j, ((Graph i).induce {v | c v = j}).IsAcyclic

open Classical in
/-- PARTITION INTO FORESTS as a decision problem over bitstrings. -/
noncomputable def partitionIntoForestsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoForestsInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoForestsFeasible i)
  | none => false

/-- **PARTITION INTO FORESTS is NP-complete.** Source: Garey and Johnson (1979), [GT14];
Hakimi and Schmeichel (1989). -/
public theorem_wanted partitionIntoForests_npComplete :
    partitionIntoForestsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoForestsDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoForests
