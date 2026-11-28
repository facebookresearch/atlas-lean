/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRID INTERSECTION GRAPH RECOGNITION: definitions

Source:
J. Kratochvíl, "A special planar satisfiability problem and a consequence of its
NP-completeness", Discrete Applied Mathematics 52(3) (1994), 233-252,
doi:10.1016/0166-218X(94)90143-0 (abstract: NP-completeness "of recognizing several classes of
intersection graphs of geometric objects in the plane, including grid intersection graphs");
definition of grid intersection graphs as in I. Ben-Arroyo Hartman, I. Newman and R. Ziv, "On grid
intersection graphs", Discrete Mathematics 87 (1991), 41-52, doi:10.1016/0012-365X(91)90069-E,
and S. Chaplick, S. Felsner, U. Hoffmann and V. Wiechert, "Grid intersection graphs and order
dimension", Order 35 (2018), 363-391, doi:10.1007/s11083-017-9437-0, Section 1.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GridIntersectionGraphRecognition

/-- An instance: the side sizes `a = |U|` and `b = |W|`, and the edge list of pairs `(u, w)`. -/
abbrev GridIntersectionGraphRecognitionInstance := ℕ × ℕ × List (ℕ × ℕ)

/-- Well-formedness of an instance: no repeated edges, and every edge `(u, w)` has `u < a` and
`w < b`. -/
def WellFormed (i : GridIntersectionGraphRecognitionInstance) : Prop :=
  i.2.2.Nodup ∧ ∀ e ∈ i.2.2, e.1 < i.1 ∧ e.2 < i.2.1

/-- The graph is a grid intersection graph: horizontal segments `h u = (y, x₁, x₂)` for `U` and
vertical segments `v w = (x, y₁, y₂)` for `W`, segments of one side pairwise disjoint, such that
`(u, w)` is an edge exactly when `h u` and `v w` meet. -/
def GridIntersectionGraphRecognitionFeasible (i : GridIntersectionGraphRecognitionInstance) :
    Prop :=
  ∃ (h : Fin i.1 → ℕ × ℕ × ℕ) (v : Fin i.2.1 → ℕ × ℕ × ℕ),
    (∀ u, (h u).2.1 ≤ (h u).2.2) ∧ (∀ w, (v w).2.1 ≤ (v w).2.2) ∧
    (∀ u u', u ≠ u' →
      (h u).1 ≠ (h u').1 ∨ (h u).2.2 < (h u').2.1 ∨ (h u').2.2 < (h u).2.1) ∧
    (∀ w w', w ≠ w' →
      (v w).1 ≠ (v w').1 ∨ (v w).2.2 < (v w').2.1 ∨ (v w').2.2 < (v w).2.1) ∧
    ∀ (u : Fin i.1) (w : Fin i.2.1), ((u : ℕ), (w : ℕ)) ∈ i.2.2 ↔
      ((h u).2.1 ≤ (v w).1 ∧ (v w).1 ≤ (h u).2.2 ∧ (v w).2.1 ≤ (h u).1 ∧ (h u).1 ≤ (v w).2.2)

open Classical in
/-- GRID INTERSECTION GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def gridIntersectionGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GridIntersectionGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ GridIntersectionGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GridIntersectionGraphRecognition
