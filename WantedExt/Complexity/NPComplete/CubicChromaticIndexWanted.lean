/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX of cubic graphs (edge 3-colorability) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (comment:
CHROMATIC INDEX, coloring the line graph, NP-complete for `K = 3` and cubic graphs, citing
Holyer's 1979 preprint) and open problem [OPEN5] CHROMATIC INDEX;
I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CubicChromaticIndex

/-!
# CHROMATIC INDEX of cubic graphs (edge 3-colorability) is NP-complete

An instance is a cubic graph `G = (V, E)`: a finite simple graph in which every vertex has
degree exactly 3. The question is whether the edges of `G` can be colored with 3 colors so
that edges sharing an endpoint get different colors, i.e. whether the chromatic index of `G`
is at most 3; for a cubic graph with at least one vertex this means exactly 3 (three edges meet
at every vertex), and by Vizing's theorem the alternative is 4. Holyer (1981) proved this
NP-complete; it is the `K = 3`, cubic case of CHROMATIC INDEX, which Garey and Johnson state as
GRAPH K-COLORABILITY of the line graph.

The graph is given by an edge list on `Fin n`. An edge coloring is a vertex coloring of the
line graph `SimpleGraph.lineGraph`, whose vertices are the edges of `G`, two being adjacent
when they are distinct and share an endpoint. Cubic is Mathlib's
`SimpleGraph.IsRegularOfDegree 3`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev CubicChromaticIndexInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CubicChromaticIndexInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges
in either orientation, no self-loops, endpoints in range), and the graph is cubic: every vertex
has degree exactly 3. -/
def WellFormed (i : CubicChromaticIndexInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsRegularOfDegree 3

/-- The edges can be colored with 3 colors, edges sharing an endpoint getting different
colors: the line graph is 3-colorable (chromatic index at most 3). -/
def CubicChromaticIndexFeasible (i : CubicChromaticIndexInstance) : Prop :=
  (Graph i).lineGraph.Colorable 3

open Classical in
/-- CHROMATIC INDEX of cubic graphs as a decision problem over bitstrings. -/
noncomputable def cubicChromaticIndexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CubicChromaticIndexInstance) x with
  | some i => decide (WellFormed i ∧ CubicChromaticIndexFeasible i)
  | none => false

/-- **CHROMATIC INDEX of cubic graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT4]; Holyer (1981). -/
public theorem_wanted cubicChromaticIndex_npComplete :
    cubicChromaticIndexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cubicChromaticIndexDec

end MetaMathlibExt.Complexity.NPComplete.CubicChromaticIndex
