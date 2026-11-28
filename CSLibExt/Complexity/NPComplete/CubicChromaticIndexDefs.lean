/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX of cubic graphs (edge 3-colorability): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (comment:
CHROMATIC INDEX, coloring the line graph, NP-complete for `K = 3` and cubic graphs, citing
Holyer's 1979 preprint) and open problem [OPEN5] CHROMATIC INDEX;
I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CubicChromaticIndex

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

end MetaMathlibExt.Complexity.NPComplete.CubicChromaticIndex
