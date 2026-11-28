/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF LINE GRAPHS: definitions

Source:
I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055 (deciding whether a cubic graph has chromatic index 3 is
NP-complete; a proper 3-edge-coloring of `H` is a proper 3-coloring of its line graph);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the parent
problem), and [OPEN5] CHROMATIC INDEX;
ISGCI, *Information System on Graph Classes and their Inclusions*, class "line" (gc_249),
problem 3-Colourability: NP-complete, with the reference to Holyer (1981).
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityLineGraphs

open GraphColoring (GraphColoringInstance Graph GraphColoringFeasible)

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ThreeColorabilityLineGraphsInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH COLORING instance with the same graph and bound `K = 3`. -/
abbrev withThreeColors (i : ThreeColorabilityLineGraphsInstance) : GraphColoringInstance :=
  (i.1, i.2, 3)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (GRAPH
COLORING's well-formedness), and the graph is a line graph. -/
def WellFormed (i : ThreeColorabilityLineGraphsInstance) : Prop :=
  GraphColoring.WellFormed (withThreeColors i) ∧
    MetaMathlibExt.SimpleGraph.IsLineGraph (Graph (withThreeColors i))

/-- The graph is properly 3-colorable. -/
def ThreeColorabilityLineGraphsFeasible (i : ThreeColorabilityLineGraphsInstance) : Prop :=
  GraphColoringFeasible (withThreeColors i)

open Classical in
/-- 3-COLORABILITY OF LINE GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeColorabilityLineGraphsInstance) x with
  | some i => decide (WellFormed i ∧ ThreeColorabilityLineGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityLineGraphs
