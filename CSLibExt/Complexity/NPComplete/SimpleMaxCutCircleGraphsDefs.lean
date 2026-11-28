/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for circle graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT (comment: SIMPLE MAX
CUT, all weights 1);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1;
C. Buchheim and L. Zheng, "Fixed linear crossing minimization by reduction to the maximum cut
problem", COCOON 2006, Lecture Notes in Computer Science 4112, 507-516,
doi:10.1007/11809678_53;
S. Masuda, K. Nakajima, T. Kashiwabara and T. Fujisawa, "Crossing minimization in linear
embeddings of graphs", IEEE Transactions on Computers 39 (1990), 124-127,
doi:10.1109/12.46286.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs
public import CSLibExt.Complexity.NPComplete.PathwidthCircleGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCircleGraphs

open MaxCut (MaxCutInstance MaxCutFeasible)

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is a circle graph, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧
    PathwidthCircleGraphs.IsCircleGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧ 0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT for circle graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutCircleGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCircleGraphs
