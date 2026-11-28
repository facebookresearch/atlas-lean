/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for circular-arc graphs: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (SIMPLE MAX CUT
for circular-arc graphs, open there);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for
the 21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (entry N [1]);
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70 (2023), 307-322, doi:10.1007/s00454-022-00472-y, Theorem 1;
R. M. McConnell, "Linear-time recognition of circular-arc graphs", Algorithmica 37 (2003),
93-147, doi:10.1007/s00453-003-1032-7;
K. S. Booth and G. S. Lueker, "Testing for the consecutive ones property, interval graphs, and
graph planarity using PQ-tree algorithms", Journal of Computer and System Sciences 13 (1976),
335-379, doi:10.1016/S0022-0000(76)80045-1.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DomaticNumberCircularArcDefs
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCircularArc

open MaxCut (MaxCutInstance MaxCutFeasible)

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
`Fin n`) whose graph is a circular-arc graph, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧
    DomaticNumberCircularArc.IsCircularArcGraph i ∧
    0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT for circular-arc graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutCircularArcDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCircularArc
