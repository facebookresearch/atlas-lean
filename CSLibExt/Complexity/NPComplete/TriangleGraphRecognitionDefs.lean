/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF TRIANGLE GRAPHS (PI* GRAPHS): definitions

Source:
G. B. Mertzios, "The recognition of triangle graphs", Theoretical Computer Science 438 (2012),
34-47, doi:10.1016/j.tcs.2012.02.042; conference version in STACS 2011, LIPIcs 9, 591-602,
doi:10.4230/LIPIcs.STACS.2011.591;
ISGCI, class "PI*" (gc_290), problem Recognition.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetCoTrapezoidGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangleGraphRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev TriangleGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TriangleGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : TriangleGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a triangle graph: each vertex `v` has a trapezoid between the lines `y = 1` and
`y = 0` with top side `[a v, b v]` and bottom side `[c v, d v]`, one of which is a single point
(so the trapezoid is a triangle with its apex on either line), and two distinct vertices are
adjacent exactly when their triangles intersect. -/
def IsTriangleGraph {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ a b c d : V → ℝ, (∀ v, a v ≤ b v ∧ c v ≤ d v ∧ (a v = b v ∨ c v = d v)) ∧
    ∀ u v, u ≠ v → (H.Adj u v ↔
      (DominatingSetCoTrapezoidGraphs.trapezoid (a u) (b u) (c u) (d u) ∩
        DominatingSetCoTrapezoidGraphs.trapezoid (a v) (b v) (c v) (d v)).Nonempty)

/-- The graph of the instance is a triangle graph. -/
def TriangleGraphRecognitionFeasible (i : TriangleGraphRecognitionInstance) : Prop :=
  IsTriangleGraph (Graph i)

open Classical in
/-- RECOGNITION OF TRIANGLE GRAPHS as a decision problem over bitstrings. -/
noncomputable def triangleGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ TriangleGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TriangleGraphRecognition
