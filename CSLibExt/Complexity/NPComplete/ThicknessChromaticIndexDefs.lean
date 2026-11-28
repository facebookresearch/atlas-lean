/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX for graphs of thickness at most k is NP-complete, for every fixed k ≥ 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN5] CHROMATIC INDEX (the
problem); I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055 (NP-complete for `K = 3` and cubic graphs); D. S. Johnson, "The
NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (CHROMATIC INDEX on thickness-`k` graphs: NP-complete,
citing Holyer).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EdgeColoringDefs
public import CSLibExt.Complexity.NPComplete.GraphThicknessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThicknessChromaticIndex

/-- Well-formedness of an instance for the thickness bound `k`: a well-formed CHROMATIC INDEX
instance (a simple edge list on `0, ..., n - 1`) whose graph has thickness at most `k`, with `0 <
K`. -/
def WellFormed (k : ℕ) (i : EdgeColoring.EdgeColoringInstance) : Prop :=
  EdgeColoring.WellFormed i ∧ GraphThickness.GraphThicknessFeasible (i.1, i.2.1, k) ∧ 0 < i.2.2

open Classical in
/-- CHROMATIC INDEX for graphs of thickness at most `k`, as a decision problem over
bitstrings. -/
noncomputable def thicknessChromaticIndexDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := EdgeColoring.EdgeColoringInstance) x with
  | some i => decide (WellFormed k i ∧ EdgeColoring.EdgeColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThicknessChromaticIndex
