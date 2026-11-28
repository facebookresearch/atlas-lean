/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLIP DISTANCE OF POINT-SET TRIANGULATIONS: definitions

Source:
A. Lubiw and V. Pathak, "Flip distance between two triangulations of a point set is
NP-complete", Computational Geometry 49 (2015), 17-23, doi:10.1016/j.comgeo.2014.11.001
(Theorem 2);
A. Pilz, "Flip distance between triangulations of a planar point set is APX-hard",
Computational Geometry 47 (2014), 589-604, doi:10.1016/j.comgeo.2014.01.001
(Lemmas 9 and 10, point sets in general position).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ConstrainedTriangulationDefs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlipDistancePointSetTriangulation

open ConstrainedTriangulation (ConstrainedTriangulationInstance SegmentsMeetAtEndpoints coord point)

/-- An instance: the number `n` of points (vertices `Fin n`), the coordinates of the points in
order (each integer coordinate `p - q` given as the pair `(p, q)`), the edge lists of `T₁` and
`T₂`, and the bound `k`. -/
abbrev FlipDistancePointSetTriangulationInstance :=
  ℕ × List ((ℕ × ℕ) × (ℕ × ℕ)) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The point set of the instance, as a `ConstrainedTriangulation` instance with no edges, so
that its `coord`, `point` and `SegmentsMeetAtEndpoints` apply. -/
abbrev pointSet (i : FlipDistancePointSetTriangulationInstance) :
    ConstrainedTriangulationInstance :=
  (i.1, [], i.2.1)

/-- `T` is a triangulation of the point set: a maximal straight-line graph on the points whose
segments meet only at common endpoints. -/
def IsTriangulation (i : FlipDistancePointSetTriangulationInstance)
    (T : SimpleGraph (Fin i.1)) : Prop :=
  Maximal (SegmentsMeetAtEndpoints (pointSet i)) T

/-- `T'` arises from `T` by removing an edge `e` of `T` and adding a different edge `f`. -/
def IsFlip {n : ℕ} (T T' : SimpleGraph (Fin n)) : Prop :=
  ∃ e ∈ T.edgeSet, ∃ f, f ≠ e ∧ T'.edgeSet = insert f (T.edgeSet \ {e})

/-- The flip graph of the point set: two triangulations are adjacent when an edge flip
transforms one into the other; graphs on `Fin n` that are not triangulations are isolated. -/
def flipGraph (i : FlipDistancePointSetTriangulationInstance) :
    SimpleGraph (SimpleGraph (Fin i.1)) :=
  SimpleGraph.fromRel fun T T' => IsTriangulation i T ∧ IsTriangulation i T' ∧ IsFlip T T'

/-- The triangulation `T₁` of the instance. -/
def T₁ (i : FlipDistancePointSetTriangulationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.2.1

/-- The triangulation `T₂` of the instance. -/
def T₂ (i : FlipDistancePointSetTriangulationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.2.2.1

/-- Well-formedness of an instance: one coordinate pair per point, pairwise distinct points, no
three points collinear, both edge lists describe simple graphs on `Fin n` (no duplicate edges in
either orientation, no self-loops, endpoints in range), `T₁` and `T₂` are triangulations of the
point set, and `k` is positive. -/
def WellFormed (i : FlipDistancePointSetTriangulationInstance) : Prop :=
  i.2.1.length = i.1 ∧ Function.Injective (coord (pointSet i)) ∧
    (∀ u v w : Fin i.1, u ≠ v → v ≠ w → u ≠ w →
      ¬ Collinear ℝ ({point (pointSet i) u, point (pointSet i) v, point (pointSet i) w} :
        Set (ℝ × ℝ))) ∧
    (i.2.2.1.Nodup ∧ ∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.1) ∧
    (i.2.2.2.1.Nodup ∧
      ∀ e ∈ i.2.2.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2.1) ∧
    IsTriangulation i (T₁ i) ∧ IsTriangulation i (T₂ i) ∧ 0 < i.2.2.2.2

/-- Some sequence of at most `k` edge flips transforms `T₁` into `T₂`: a walk of length at most
`k` from `T₁` to `T₂` in the flip graph. -/
def FlipDistancePointSetTriangulationFeasible
    (i : FlipDistancePointSetTriangulationInstance) : Prop :=
  ∃ p : (flipGraph i).Walk (T₁ i) (T₂ i), p.length ≤ i.2.2.2.2

open Classical in
/-- FLIP DISTANCE OF POINT-SET TRIANGULATIONS as a decision problem over bitstrings. -/
noncomputable def flipDistancePointSetTriangulationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FlipDistancePointSetTriangulationInstance) x with
  | some i => decide (WellFormed i ∧ FlipDistancePointSetTriangulationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FlipDistancePointSetTriangulation
