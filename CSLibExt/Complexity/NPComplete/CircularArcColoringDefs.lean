/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY of circular-arc graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (comment:
NP-complete for circular arc graphs, even given their representation as families of arcs);
M. R. Garey, D. S. Johnson, G. L. Miller and C. H. Papadimitriou, "The complexity of coloring
circular arcs and chords", SIAM Journal on Algebraic and Discrete Methods 1(2) (1980), 216-227,
doi:10.1137/0601025.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularArcColoring

/-- An instance: the number `L` of points on the circle, the arcs (clockwise from the first
endpoint to the second), and the number `K` of colors. -/
abbrev CircularArcColoringInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The point `p` lies on the arc `(a, b)` running clockwise from `a` to `b`. -/
def OnArc (arc : ℕ × ℕ) (p : ℕ) : Prop :=
  if arc.1 ≤ arc.2 then arc.1 ≤ p ∧ p ≤ arc.2 else arc.1 ≤ p ∨ p ≤ arc.2

/-- Arcs `j` and `k` of the family meet: some point of the circle lies on both. -/
def Meet (i : CircularArcColoringInstance) (j k : Fin i.2.1.length) : Prop :=
  ∃ p < i.1, OnArc i.2.1[j] p ∧ OnArc i.2.1[k] p

/-- Well-formedness of an instance: every arc endpoint is one of the `L` points, and
`0 < K ≤ |V|`, the number of arcs. -/
def WellFormed (i : CircularArcColoringInstance) : Prop :=
  (∀ arc ∈ i.2.1, arc.1 < i.1 ∧ arc.2 < i.1) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- The intersection graph is `K`-colorable: the arcs get colors `0, …, K - 1` with any two
distinct meeting arcs colored differently. -/
def CircularArcColoringFeasible (i : CircularArcColoringInstance) : Prop :=
  ∃ f : Fin i.2.1.length → Fin i.2.2, ∀ j k, j ≠ k → Meet i j k → f j ≠ f k

open Classical in
/-- GRAPH K-COLORABILITY of circular-arc graphs as a decision problem over bitstrings. -/
noncomputable def circularArcColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CircularArcColoringInstance) x with
  | some i => decide (WellFormed i ∧ CircularArcColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CircularArcColoring
