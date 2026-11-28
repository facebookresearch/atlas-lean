/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on tripartite graphs: definitions

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Technical Report
RUU-CS-91-39, Department of Computer Science, Utrecht University (1991), abstract (SIMPLE MAX CUT
"is NP-complete when restricted to one of the following classes: chordal graphs, undirected path
graphs, split graphs, tripartite graphs, and graphs that are the complement of a bipartite
graph"); conference version STACS 94, LNCS 775 (1994), 769-780,
doi:10.1007/3-540-57785-8_189; journal version Nordic Journal of Computing 7(1) (2000), 14-31.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTripartite

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is tripartite (3-colorable), and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).Colorable 3 ∧ 0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT on tripartite graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutTripartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTripartite
