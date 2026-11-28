/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for undirected path graphs: definitions

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Technical Report
RUU-CS-91-39, Department of Computer Science, Utrecht University (1991), abstract (SIMPLE MAX CUT
"is NP-complete when restricted to one of the following classes: chordal graphs, undirected path
graphs, split graphs, tripartite graphs, and graphs that are the complement of a bipartite
graph"); conference version STACS 94, LNCS 775 (1994), 769-780,
doi:10.1007/3-540-57785-8_189; journal version Nordic Journal of Computing 7(1) (2000), 14-31;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021,
Table 1 (MAX CUT on UNDIRECTED PATH graphs: N [20], [20] = Bodlaender and Jansen).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsDefs
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutUndirectedPathGraphs

open MaxCut (MaxCutInstance MaxCutFeasible)

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
`Fin n`) whose graph is an undirected path graph, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧
    DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph
      (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT for undirected path graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutUndirectedPathGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutUndirectedPathGraphs
