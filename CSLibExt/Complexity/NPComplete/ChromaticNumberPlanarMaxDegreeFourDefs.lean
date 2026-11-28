/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER for planar graphs of maximum degree 4: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC NUMBER),
p. 191, comment ("remains NP-complete ... for K = 3, for planar graphs having no vertex degree
exceeding 4");
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticNumberPlanarMaxDegreeFour

open MetaMathlibExt.Complexity.NPComplete.GraphColoring
  (GraphColoringInstance Graph GraphColoringFeasible)

open Classical in
/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with
`0 < K ≤ |V|` whose graph is planar with every vertex degree at most 4. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).IsPlanar ∧
    ∀ v, (Graph i).degree v ≤ 4

open Classical in
/-- CHROMATIC NUMBER for planar graphs of maximum degree 4 as a decision problem over
bitstrings. -/
noncomputable def chromaticNumberPlanarMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChromaticNumberPlanarMaxDegreeFour
