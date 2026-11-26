/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH IN LINE GRAPHS is NP-complete

Source:
A. A. Bertossi, "The edge Hamiltonian path problem is NP-complete", Information Processing
Letters 13 (1981), 157-159, doi:10.1016/0020-0190(81)90048-X;
recorded in M. Lampis, K. Makino, V. Mitsou and Y. Uno, "Parameterized edge Hamiltonicity",
Discrete Applied Mathematics 248 (2018), 68-78, doi:10.1016/j.dam.2017.04.045, Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LineGraphHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance WellFormed HamiltonianPathUndirectedFeasible)

/-!
# HAMILTONIAN PATH IN LINE GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected).
QUESTION: does the line graph `L(G)` have a Hamiltonian path, that is, is there an ordering of
all the edges of `G` in which every two consecutive edges share an endpoint?

Bertossi proves this EDGE HAMILTONIAN PATH problem NP-complete. Lampis, Makino, Mitsou and Uno
(Section 1) state it as "given an undirected graph `G(V, E)`, does there exist a permutation of
`E` such that every two consecutive edges in the permutation share an endpoint?", which
"corresponds to the restriction of (vertex) Hamiltonian Path to line graphs", and record that it
"has long been known to be NP-complete" (citing Bertossi).

The graph `G` is a HAMILTONIAN PATH (UNDIRECTED) instance of
`WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted` (vertex count and simple edge
list), well formed in that module's sense (`HamiltonianPathUndirected.WellFormed`). Its line graph
is passed
to the same module as the instance whose vertices are the edge positions `0, …, |E| - 1` and
whose edge list `lineEdges` contains the pairs `a < b` of positions whose edges share an
endpoint; this is the adjacency of Mathlib's `SimpleGraph.lineGraph` (distinct edges with a
common endpoint), and the question is that module's `HamiltonianPathUndirectedFeasible` for it.
The edge list of `G` has no repeated edge and no reversed copy, so distinct positions are distinct
edges. For `E = ∅` the empty permutation qualifies, and the empty list is a Hamiltonian path of the
line-graph instance with no vertices, so edgeless graphs are yes-instances.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Two edges, given as vertex pairs, share an endpoint. -/
abbrev ShareEndpoint (e f : ℕ × ℕ) : Prop :=
  e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2

/-- The edges of the line graph: the pairs `(a, b)` of edge positions with `a < b < |E|` whose
edges share an endpoint. -/
def lineEdges (i : HamiltonianPathUndirectedInstance) : List (ℕ × ℕ) :=
  (List.range i.2.length).flatMap fun a =>
    ((List.range i.2.length).filter fun b =>
      decide (a < b ∧ ShareEndpoint (i.2.getD a (0, 0)) (i.2.getD b (0, 0)))).map fun b => (a, b)

/-- The line graph of `G` as a HAMILTONIAN PATH (UNDIRECTED) instance: `|E|` vertices and the
line-graph edges. -/
def toLineGraphInstance (i : HamiltonianPathUndirectedInstance) :
    HamiltonianPathUndirectedInstance :=
  (i.2.length, lineEdges i)

open Classical in
/-- HAMILTONIAN PATH IN LINE GRAPHS as a decision problem over bitstrings. -/
noncomputable def lineGraphHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible (toLineGraphInstance i))
  | none => false

/-- **HAMILTONIAN PATH IN LINE GRAPHS is NP-complete.** Source: Bertossi (1981). -/
public theorem_wanted lineGraphHamiltonianPath_npComplete :
    lineGraphHamiltonianPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lineGraphHamiltonianPathDec

end MetaMathlibExt.Complexity.NPComplete.LineGraphHamiltonianPath
