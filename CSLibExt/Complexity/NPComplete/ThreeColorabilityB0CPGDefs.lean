/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF B0-CPG GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY, the problem
restricted here;
Z. Deniz, E. Galby, A. Munaro and B. Ries, "On contact graphs of paths on a grid", Graph Drawing
and Network Visualization (GD 2018), Lecture Notes in Computer Science 11282 (2018), 317-330,
doi:10.1007/978-3-030-04414-5_22, Theorem 5 (arXiv:1803.03468).
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityB0CPG

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- A grid point `p ∈ ℤ × ℤ` as a point of the plane `ℝ × ℝ`. -/
def gridPoint (p : ℤ × ℤ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

/-- The path of vertex `v`: the closed straight segment from `A v` to `B v`. -/
def gridPath {n : ℕ} (A B : Fin n → ℤ × ℤ) (v : Fin n) : Set (ℝ × ℝ) :=
  segment ℝ (gridPoint (A v)) (gridPoint (B v))

/-- The interior of the path of vertex `v`: its points other than its two endpoints. -/
def pathInterior {n : ℕ} (A B : Fin n → ℤ × ℤ) (v : Fin n) : Set (ℝ × ℝ) :=
  gridPath A B v \ {gridPoint (A v), gridPoint (B v)}

/-- `A`, `B` give a `B_0`-CPG representation of `G`: every path is a straight horizontal or
vertical grid segment between two distinct grid points (no bend), distinct paths have disjoint
interiors, and two distinct vertices are adjacent exactly when their paths touch, i.e. share a
grid point that is an endpoint of at least one of the two paths. -/
def IsB0CPGRepresentation {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Fin n → ℤ × ℤ) : Prop :=
  (∀ v, A v ≠ B v ∧ ((A v).1 = (B v).1 ∨ (A v).2 = (B v).2)) ∧
    (∀ u v, u ≠ v → Disjoint (pathInterior A B u) (pathInterior A B v)) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ ∃ p : ℤ × ℤ, gridPoint p ∈ gridPath A B u ∧
      gridPoint p ∈ gridPath A B v ∧ (p = A u ∨ p = B u ∨ p = A v ∨ p = B v))

/-- `G` is a `B_0`-CPG graph: it has a `B_0`-CPG representation. -/
def IsB0CPG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ A B : Fin n → ℤ × ℤ, IsB0CPGRepresentation G A B

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `K = 3`
whose graph is a `B_0`-CPG graph. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ IsB0CPG (Graph i)

open Classical in
/-- 3-COLORABILITY OF B0-CPG GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityB0CPGDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityB0CPG
