/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL COLORING is NP-complete

Source:
A. Sánchez-Arroyo, "Determining the total colouring number is NP-hard", Discrete Mathematics
78 (1989), 315-319, doi:10.1016/0012-365X(89)90187-8;
C. J. H. McDiarmid and A. Sánchez-Arroyo, "Total colouring regular bipartite graphs is
NP-hard", Discrete Mathematics 124 (1994), 155-162, doi:10.1016/0012-365X(92)00058-Y.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalColoring

/-!
# TOTAL COLORING is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a total coloring of `G` with at most `K` colors, that is, a map
`V ∪ E → {1, …, K}` that gives distinct colors to adjacent vertices, to edges sharing an
endpoint, and to each edge and each of its endpoints? Equivalently, is the total chromatic
number `χ''(G)` at most `K`?

Sánchez-Arroyo proves that deciding whether `χ''(G) = Δ(G) + 1` is NP-complete, by a reduction
from edge coloring; McDiarmid and Sánchez-Arroyo prove it for regular bipartite graphs. Since
`χ''(G) ≥ Δ(G) + 1` always, these are the instances of the problem stated here with
`K = Δ(G) + 1`; membership in NP is immediate (a coloring is a certificate).

A total coloring with colors `Fin K` is a pair of Mathlib colorings: a proper vertex coloring
`(Graph i).Coloring (Fin K)` (adjacent vertices get distinct colors) and a proper coloring of
the line graph `(Graph i).lineGraph.Coloring (Fin K)` (its vertices are the edges of the graph,
adjacent when they share an endpoint), such that no edge has the color of one of its endpoints.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, number of colors `K`. -/
abbrev TotalColoringInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TotalColoringInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : TotalColoringInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- A total coloring with `K` colors: a proper vertex coloring `cv` and a proper edge coloring
`ce` (a coloring of the line graph) such that every edge `e` and every endpoint `v ∈ e` get
distinct colors. -/
def TotalColoringFeasible (i : TotalColoringInstance) : Prop :=
  ∃ (cv : (Graph i).Coloring (Fin i.2.2)) (ce : (Graph i).lineGraph.Coloring (Fin i.2.2)),
    ∀ e : (Graph i).edgeSet, ∀ v ∈ (e : Sym2 (Fin i.1)), ce e ≠ cv v

open Classical in
/-- TOTAL COLORING as a decision problem over bitstrings. -/
noncomputable def totalColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TotalColoringInstance) x with
  | some i => decide (WellFormed i ∧ TotalColoringFeasible i)
  | none => false

/-- **TOTAL COLORING is NP-complete.** Source: Sánchez-Arroyo (1989); McDiarmid and
Sánchez-Arroyo (1994). -/
public theorem_wanted totalColoring_npComplete :
    totalColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalColoringDec

end MetaMathlibExt.Complexity.NPComplete.TotalColoring
