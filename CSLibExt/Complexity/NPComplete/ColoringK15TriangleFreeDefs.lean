/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY on (K_1,5, triangle)-free graphs: definitions

Source:
F. Maffray and M. Preissmann, "On the NP-completeness of the k-colorability problem for
triangle-free graphs", Discrete Mathematics 162 (1996), 313-317,
doi:10.1016/S0012-365X(97)89267-9 (3-colorability is NP-complete for triangle-free graphs of
maximum degree 4);
P. A. Golovach, M. Johnson, D. Paulusma, and J. Song, "A survey on the computational complexity
of coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, Theorem 16 and Theorem 21(i).6 ("3-Colouring is NP-complete for
(C₃, K₁,ᵣ)-free graphs for all r ≥ 5");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ColoringK15TriangleFree

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance (a simple graph
given by an edge list), `K` is positive, the graph has no triangle, and `K_{1,5}` is not an
induced subgraph of it. -/
def WellFormed (i : GraphColoring.GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ (GraphColoring.Graph i).CliqueFree 3 ∧
    ¬ (completeBipartiteGraph (Fin 1) (Fin 5)).IsIndContained (GraphColoring.Graph i)

open Classical in
/-- GRAPH K-COLORABILITY on `(K_{1,5}, triangle)`-free graphs as a decision problem over
bitstrings. -/
noncomputable def coloringK15TriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ColoringK15TriangleFree
