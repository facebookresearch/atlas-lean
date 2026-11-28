/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY on dually chordal graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER) (the parent problem);
A. Leitert, "3-Colourability of dually chordal graphs in linear time", arXiv:1206.0233 (2012),
Theorem 1 (4-COLOURABILITY is NP-complete for dually chordal graphs);
A. Brandstädt, V. D. Chepoi and F. F. Dragan, "The algorithmic use of hypertree structure and
maximum neighbourhood orderings", Discrete Applied Mathematics 82(1-3) (1998), 43-77,
doi:10.1016/s0166-218x(97)00125-x (cited by Wikipedia, "Dually chordal graph", for this
result);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_185` (dually
chordal), problem Colourability: NP-complete (note `ref_1504`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import CSLibExt.Complexity.NPComplete.IndependentSetDuallyChordalDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringDuallyChordal

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)
open IndependentSetDuallyChordal (DuallyChordal)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`GraphColoring.WellFormed`), `0 < K ≤ |V|`, and the graph is dually chordal. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (0 < i.2.2 ∧ i.2.2 ≤ i.1) ∧ DuallyChordal (Graph i)

open Classical in
/-- GRAPH K-COLORABILITY on dually chordal graphs as a decision problem over bitstrings. -/
noncomputable def graphColoringDuallyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphColoringDuallyChordal
