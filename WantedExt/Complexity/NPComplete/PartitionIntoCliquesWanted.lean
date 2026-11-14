/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO
CLIQUES;
R. M. Karp, "Reducibility among combinatorial problems", in R. E. Miller and
J. W. Thatcher (eds.), *Complexity of Computer Computations*, Plenum Press
(1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (as CLIQUE COVER).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques

/-!
# PARTITION INTO CLIQUES is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: can the vertices of
`G` be partitioned into `k ≤ K` disjoint sets `V₁, ..., Vₖ` such that, for `1 ≤ i ≤ k`, the
subgraph induced by `Vᵢ` is a complete graph?

The partition is given by the map `c : V → Fin k` sending each vertex to the index of its
block, so `Vⱼ = c⁻¹(j)`; "induces a complete graph" is Mathlib's `IsClique`. An empty block is
allowed; dropping it gives a partition with fewer blocks, so this does not change the answer.
Equivalently, the complement of `G` is `K`-colorable; the statement uses cliques directly, as
the source does.

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
abbrev PartitionIntoCliquesInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PartitionIntoCliquesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |V| = n`. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- The vertices split into at most `K` cliques: for some `k ≤ K` there is a partition into
blocks `c⁻¹(j)`, `j : Fin k`, each of which is a clique of the graph. -/
def PartitionIntoCliquesFeasible (i : PartitionIntoCliquesInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ c : Fin i.1 → Fin k, ∀ j : Fin k, (Graph i).IsClique {v | c v = j}

open Classical in
/-- PARTITION INTO CLIQUES as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES is NP-complete.** Source: Garey and Johnson (1979), [GT15];
Karp (1972). -/
public theorem_wanted partitionIntoCliques_npComplete :
    partitionIntoCliquesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques
