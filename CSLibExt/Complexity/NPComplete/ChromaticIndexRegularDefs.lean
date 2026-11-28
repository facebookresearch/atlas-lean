/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX of k-regular graphs (fixed k ≥ 3): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN5] CHROMATIC INDEX;
I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055 (`k = 3`);
D. Leven and Z. Galil, "NP completeness of finding the chromatic index of regular graphs",
Journal of Algorithms 4(1) (1983), 35-44, doi:10.1016/0196-6774(83)90032-9 (`k ≥ 4`);
restated as Theorem 2 of E. Galby, P. T. Lima, D. Paulusma and B. Ries, "Classifying
k-Edge Colouring for H-free graphs", Information Processing Letters 146 (2019), 39-43,
doi:10.1016/j.ipl.2019.02.006 (arXiv:1810.04379).
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

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexRegular

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ChromaticIndexRegularInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ChromaticIndexRegularInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

open Classical in
/-- Well-formedness of an instance for the fixed degree `k`: the edge list describes a simple
graph (no duplicate edges in either orientation, no self-loops, endpoints in range), and the
graph is `k`-regular: every vertex has degree exactly `k`. -/
def WellFormed (k : ℕ) (i : ChromaticIndexRegularInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsRegularOfDegree k

/-- The edges can be colored with `k` colors, edges sharing an endpoint getting different
colors: the line graph is `k`-colorable (chromatic index at most `k`). -/
def ChromaticIndexRegularFeasible (k : ℕ) (i : ChromaticIndexRegularInstance) : Prop :=
  (Graph i).lineGraph.Colorable k

open Classical in
/-- CHROMATIC INDEX of `k`-regular graphs, for the fixed `k`, as a decision problem over
bitstrings. -/
noncomputable def chromaticIndexRegularDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChromaticIndexRegularInstance) x with
  | some i => decide (WellFormed k i ∧ ChromaticIndexRegularFeasible k i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexRegular
