/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLIP DISTANCE OF POINT-SET TRIANGULATIONS is NP-complete

Source:
A. Lubiw and V. Pathak, "Flip distance between two triangulations of a point set is
NP-complete", Computational Geometry 49 (2015), 17-23, doi:10.1016/j.comgeo.2014.11.001
(Theorem 2);
A. Pilz, "Flip distance between triangulations of a planar point set is APX-hard",
Computational Geometry 47 (2014), 589-604, doi:10.1016/j.comgeo.2014.01.001
(Lemmas 9 and 10, point sets in general position).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ConstrainedTriangulationWanted
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlipDistancePointSetTriangulation

open ConstrainedTriangulation (ConstrainedTriangulationInstance SegmentsMeetAtEndpoints coord point)

/-!
# FLIP DISTANCE OF POINT-SET TRIANGULATIONS is NP-complete

INSTANCE: a finite set `S` of points in the plane with integer coordinates, no three of them
collinear, two triangulations `T₁` and `T₂` of `S`, and a positive integer `k`.
QUESTION: can `T₁` be transformed into `T₂` by at most `k` edge flips?

Definitions follow Pilz (2014), §1: "a triangulation `T` of `S` is a maximal straight-line
crossing-free graph on `S`. An edge flip is the operation of removing an edge `e` of `T` and
adding a different edge `f` such that the resulting graph is again a triangulation of `S`";
the flip graph of `S` has the triangulations of `S` as vertices, two of them adjacent when one
flip transforms one into the other, and the flip distance is the length of a shortest path
in it. Lubiw and Pathak (2015), Theorem 2, prove the question NP-complete for point sets in
the plane; Pilz proves it for point sets in general position (no three points collinear), his
standing assumption, under which "crossing-free" is unambiguous. The instance class here is
Pilz's: the points are pairwise distinct and no three are collinear (Mathlib's `Collinear`).

The points are the vertices `Fin n`, with integer coordinates. A straight-line graph on the
point set is a `SimpleGraph (Fin n)`, an edge `{v, w}` standing for the closed segment between
the points of `v` and `w`. Crossing-free (segments meet only at common endpoints) and the
triangulation as a maximal such graph are reused from `ConstrainedTriangulationWanted`
(`SegmentsMeetAtEndpoints`, Mathlib's `Maximal`), which states Lloyd's definition of a
triangulation of a point set. `T₁` and `T₂` are given as edge lists. The flip graph is a
`SimpleGraph` on the graphs over `Fin n` (`SimpleGraph.fromRel`, the flip relation is
symmetric), whose only edges join triangulations, and "at most `k` flips" is a walk of length
at most `k` in it (Mathlib's `SimpleGraph.Walk`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. An integer coordinate is a pair
`(p, q)` of naturals standing for `p - q`; numbers use the canonical binary encoding.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **FLIP DISTANCE OF POINT-SET TRIANGULATIONS is NP-complete.** Source: Lubiw and Pathak
(2015), Theorem 2; Pilz (2014), point sets in general position. -/
public theorem_wanted flipDistancePointSetTriangulation_npComplete :
    flipDistancePointSetTriangulationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L flipDistancePointSetTriangulationDec

end MetaMathlibExt.Complexity.NPComplete.FlipDistancePointSetTriangulation
