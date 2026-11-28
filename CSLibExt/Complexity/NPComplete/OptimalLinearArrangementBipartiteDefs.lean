/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL LINEAR ARRANGEMENT for bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT42] OPTIMAL LINEAR ARRANGEMENT,
comment: "Remains NP-complete if G is bipartite [Even and Shiloach, 1975]" (S. Even and
Y. Shiloach, "NP-completeness of several arrangement problems", Technical Report 43, Department
of Computer Science, Technion, Haifa (1975); the report itself was not available).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumLinearArrangementDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalLinearArrangementBipartite

open MinimumLinearArrangement (MinimumLinearArrangementInstance
  MinimumLinearArrangementFeasible)

/-- Well-formedness of an instance: a well-formed OPTIMAL LINEAR ARRANGEMENT instance (a simple
edge list on `0, …, n - 1`) whose graph is bipartite, and `0 < K`. -/
def WellFormed (i : MinimumLinearArrangementInstance) : Prop :=
  MinimumLinearArrangement.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsBipartite ∧ 0 < i.2.2

open Classical in
/-- OPTIMAL LINEAR ARRANGEMENT for bipartite graphs as a decision problem over bitstrings. -/
noncomputable def optimalLinearArrangementBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ MinimumLinearArrangementFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OptimalLinearArrangementBipartite
