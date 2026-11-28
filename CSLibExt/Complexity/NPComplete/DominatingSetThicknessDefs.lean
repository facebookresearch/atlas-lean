/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on graphs of thickness at most k (fixed k ≥ 1): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET, comment
("Remains NP-complete for planar graphs with maximum vertex degree 3 [...]");
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 5(1)
(1984), 147-160, doi:10.1016/0196-6774(84)90045-2, Section 3 (the result was proved for 3-regular
planar graphs, also by Kikuno and Kakuda; the "regular of degree 4" class that [GT2] also lists
was a transcription error);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 (thickness-k graphs) and Table 1
(thickness-k graphs, DOMINATING SET: NP-complete, citing Garey and Johnson).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs
public import CSLibExt.Complexity.NPComplete.GraphThicknessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetThickness

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-- The GRAPH THICKNESS instance with the same vertex count and edge list and the bound `k`. -/
def withThickness (k : ℕ) (i : DominatingSetInstance) : GraphThickness.GraphThicknessInstance :=
  (i.1, i.2.1, k)

/-- Well-formedness of an instance for the fixed thickness bound `k`: a well-formed DOMINATING
SET instance (a simple edge list on `Fin n`) whose graph has thickness at most `k`, with
`0 < K ≤ |V| = n`. -/
def WellFormed (k : ℕ) (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ GraphThickness.GraphThicknessFeasible (withThickness k i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- DOMINATING SET on graphs of thickness at most `k`, for the fixed `k`, as a decision problem
over bitstrings. -/
noncomputable def dominatingSetThicknessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed k i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetThickness
