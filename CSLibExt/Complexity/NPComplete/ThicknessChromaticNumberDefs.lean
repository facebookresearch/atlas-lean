/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER for graphs of thickness at most k is NP-complete, for every fixed k ≥ 1: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (comment:
NP-complete for `K = 3` and planar graphs with no vertex degree exceeding 4);
L. Stockmeyer, "Planar 3-colorability is polynomial complete", ACM SIGACT News 5(3) (1973),
19-25, doi:10.1145/1008293.1008294;
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (CHROMATIC NUMBER on thickness-`k` graphs: NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import CSLibExt.Complexity.NPComplete.GraphThicknessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThicknessChromaticNumber

/-- Well-formedness of an instance for the thickness bound `k`: a well-formed GRAPH K-COLORABILITY
instance (a simple edge list on `0, ..., n - 1`) whose graph has thickness at most `k`, with `0 < K
≤ n`. -/
def WellFormed (k : ℕ) (i : GraphColoring.GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ GraphThickness.GraphThicknessFeasible (i.1, i.2.1, k) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CHROMATIC NUMBER for graphs of thickness at most `k`, as a decision problem over
bitstrings. -/
noncomputable def thicknessChromaticNumberDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed k i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThicknessChromaticNumber
