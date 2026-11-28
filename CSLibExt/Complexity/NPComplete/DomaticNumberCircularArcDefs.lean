/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMATIC NUMBER of circular-arc graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT3] DOMATIC NUMBER;
M. A. Bonuccelli, "Dominating sets and domatic number of circular arc graphs", Discrete Applied
Mathematics 12 (1985), 203-213, doi:10.1016/0166-218X(85)90025-3;
A. Sprague, "NP-completeness of the domatic number problem on circular arc graphs", Proceedings
of the 37th Annual ACM Southeast Regional Conference (1999), doi:10.1145/306363.306416.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CircularArcColoringDefs
public import CSLibExt.Complexity.NPComplete.DomaticNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DomaticNumberCircularArc

open MetaMathlibExt.Complexity.NPComplete

/-- `G` is a circular-arc graph: for some `L`, the vertices carry closed arcs with endpoints
among the `L` points of the circle such that two distinct vertices are adjacent exactly when
their arcs meet. -/
def IsCircularArcGraph (i : DomaticNumber.DomaticNumberInstance) : Prop :=
  ∃ L : ℕ, ∃ arc : Fin i.1 → ℕ × ℕ, (∀ v, (arc v).1 < L ∧ (arc v).2 < L) ∧
    ∀ u v, u ≠ v → ((DomaticNumber.Graph i).Adj u v ↔
      ∃ p < L, CircularArcColoring.OnArc (arc u) p ∧ CircularArcColoring.OnArc (arc v) p)

/-- Well-formedness of an instance: well formed for DOMATIC NUMBER (a simple graph and
`0 < K ≤ |V|`), and the graph is a circular-arc graph. -/
def WellFormed (i : DomaticNumber.DomaticNumberInstance) : Prop :=
  DomaticNumber.WellFormed i ∧ IsCircularArcGraph i

open Classical in
/-- DOMATIC NUMBER of circular-arc graphs as a decision problem over bitstrings. -/
noncomputable def domaticNumberCircularArcDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DomaticNumber.DomaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ DomaticNumber.DomaticNumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DomaticNumberCircularArc
