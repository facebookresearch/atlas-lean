/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNICONNECTED SUBGRAPH for acyclic directed graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT30] UNICONNECTED SUBGRAPH, comment;
S. N. Maheshwari, "Traversal marker placement problems are NP-complete", Technical Report
CU-CS-092-76, Department of Computer Science, University of Colorado, Boulder (1976),
p. 2 and Lemma 1, https://scholar.colorado.edu/concern/reports/rb68xc64n.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UniconnectedSubgraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniconnectedSubgraphAcyclic

open UniconnectedSubgraph (UniconnectedSubgraphInstance Graph UniconnectedSubgraphFeasible)

/-!
# UNICONNECTED SUBGRAPH for acyclic directed graphs is NP-complete

INSTANCE: an acyclic directed graph `G = (V, A)` and a positive integer `K ≤ |A|`.
QUESTION: is there a subset `A' ⊆ A` with `|A'| ≥ K` such that `G' = (V, A')` has at most one
directed path between any pair of vertices?

Garey and Johnson record in the comment to [GT30] that UNICONNECTED SUBGRAPH "remains
NP-complete for acyclic directed graphs". Maheshwari's report, which [GT30] cites, works with
acyclic flow graphs throughout ("In what follows we consider acyclic flow graphs only", p. 2),
and the digraph of its Lemma 1, built from a VERTEX COVER instance, is acyclic: its arcs go from
the source to `u₀` and `u₁`, from `u₁` to the vertices of the undirected graph, from those
vertices and from `u₀` to its edges, and from its edges to the sink. A subdigraph with at least
`K` arcs and at most one directed path between any two vertices is a polynomial certificate,
and acyclicity is decidable in polynomial time, so the problem is in NP.

The instance, the digraph, the parent well-formedness (a loop-free arc list without duplicates
on the vertices `0, ..., n - 1`, and `0 < K ≤ |A|`) and the question are those of
UNICONNECTED SUBGRAPH (`UniconnectedSubgraph.UniconnectedSubgraphInstance`,
`UniconnectedSubgraph.Graph`, `UniconnectedSubgraph.WellFormed`,
`UniconnectedSubgraph.UniconnectedSubgraphFeasible`), reused unchanged. The restriction adds
to `WellFormed` that `G` is acyclic: no vertex reaches itself by one or more arcs
(`∀ v, ¬ Relation.TransGen (Graph i).Adj v v`), as in `CodeGenerationOnAOneRegisterMachineWanted`
and `FaultDetectionDirectedGraphsWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed UNICONNECTED SUBGRAPH instance (a loop-free arc
list without duplicates on `Fin n`, and `0 < K ≤ |A|`) whose digraph is acyclic: no vertex
reaches itself by a nonempty sequence of arcs. -/
def WellFormed (i : UniconnectedSubgraphInstance) : Prop :=
  UniconnectedSubgraph.WellFormed i ∧ ∀ v, ¬ Relation.TransGen (Graph i).Adj v v

open Classical in
/-- UNICONNECTED SUBGRAPH for acyclic directed graphs as a decision problem over bitstrings. -/
noncomputable def uniconnectedSubgraphAcyclicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniconnectedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ UniconnectedSubgraphFeasible i)
  | none => false

/-- **UNICONNECTED SUBGRAPH for acyclic directed graphs is NP-complete.** Source: Garey and
Johnson (1979), [GT30]; Maheshwari (1976), Lemma 1. -/
public theorem_wanted uniconnectedSubgraphAcyclic_npComplete :
    uniconnectedSubgraphAcyclicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L uniconnectedSubgraphAcyclicDec

end MetaMathlibExt.Complexity.NPComplete.UniconnectedSubgraphAcyclic
