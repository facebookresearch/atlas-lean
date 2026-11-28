/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on graphs of thickness at most k (fixed k ≥ 2): definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 ("SIMPLE MAX CUT becomes NP-hard
for k = 2 also (even if G is such that deleting a single vertex makes it planar) [7]", where [7]
is F. Barahona, "On the complexity of max cut", Report No. 186, Université Scientifique et
Médicale et Institut National Polytechnique de Grenoble (1980)) and Table 1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT, comment ("Remains
NP-complete if `w(e) = 1` for all `e ∈ E` (the SIMPLE MAX CUT problem) [...], and if, in
addition, no vertex has degree exceeding 3 [Yannakakis, 1978b]");
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th Annual ACM
Symposium on Theory of Computing (1978), 253-264, doi:10.1145/800133.804355;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphThicknessDefs
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutThickness

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-- An instance: the vertex count `n`, the edge list, and the bound `K`; this is the MAXIMUM
CUT instance type. -/
abbrev SimpleMaxCutThicknessInstance := MaxCutInstance

/-- The GRAPH THICKNESS instance with the same vertex count and edge list and the bound `k`. -/
def withThickness (k : ℕ) (i : SimpleMaxCutThicknessInstance) :
    GraphThickness.GraphThicknessInstance :=
  (i.1, i.2.1, k)

/-- Well-formedness of an instance for the fixed thickness bound `k`: a well-formed MAXIMUM CUT
instance (a simple edge list on the vertices `0, ..., n - 1`) whose graph has thickness at most
`k`, and `0 < K`. -/
def WellFormed (k : ℕ) (i : SimpleMaxCutThicknessInstance) : Prop :=
  MaxCut.WellFormed i ∧ GraphThickness.GraphThicknessFeasible (withThickness k i) ∧ 0 < i.2.2

/-- A partition `V₁ = S`, `V₂ = V - S` with at least `K` edges between the two sets (the
MAXIMUM CUT question). -/
def SimpleMaxCutThicknessFeasible (i : SimpleMaxCutThicknessInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on graphs of thickness at most `k`, for the fixed `k`, as a decision problem
over bitstrings. -/
noncomputable def simpleMaxCutThicknessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimpleMaxCutThicknessInstance) x with
  | some i => decide (WellFormed k i ∧ SimpleMaxCutThicknessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutThickness
