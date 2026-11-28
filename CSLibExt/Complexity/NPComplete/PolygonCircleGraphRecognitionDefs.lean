/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF POLYGON-CIRCLE GRAPHS: definitions

Source:
M. Pergel, "Recognition of polygon-circle graphs and graphs of interval filaments is
NP-complete", Graph-Theoretic Concepts in Computer Science (WG 2007), LNCS 4769 (2007), 238-247,
doi:10.1007/978-3-540-74839-7_23;
M. Koebe, "On a new class of intersection graphs", Fourth Czechoslovakian Symposium on
Combinatorics, Graphs and Complexity, Annals of Discrete Mathematics 51 (1992), 141-143,
doi:10.1016/S0167-5060(08)70618-6 (the class, as spider graphs).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolygonCircleGraphRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev PolygonCircleGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PolygonCircleGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : PolygonCircleGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `C` is a polygon-circle representation of `G`: every `C v` is a set of at least three points
of the unit circle (the corners of the inscribed convex polygon `convexHull ℝ (C v)`), and two
distinct vertices are adjacent if and only if their polygons intersect. -/
def IsPolygonCircleRepresentation {V : Type*} (G : SimpleGraph V) (C : V → Finset (ℝ × ℝ)) :
    Prop :=
  (∀ v, 3 ≤ (C v).card ∧ ∀ p ∈ C v, p.1 ^ 2 + p.2 ^ 2 = 1) ∧
    ∀ u v, u ≠ v →
      (G.Adj u v ↔
        (convexHull ℝ (C u : Set (ℝ × ℝ)) ∩ convexHull ℝ (C v : Set (ℝ × ℝ))).Nonempty)

/-- The graph of the instance is a polygon-circle graph. -/
def PolygonCircleGraphRecognitionFeasible (i : PolygonCircleGraphRecognitionInstance) : Prop :=
  ∃ C : Fin i.1 → Finset (ℝ × ℝ), IsPolygonCircleRepresentation (Graph i) C

open Classical in
/-- RECOGNITION OF POLYGON-CIRCLE GRAPHS as a decision problem over bitstrings. -/
noncomputable def polygonCircleGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolygonCircleGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ PolygonCircleGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PolygonCircleGraphRecognition
