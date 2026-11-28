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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FlipDistancePointSetTriangulationDefs

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

/-- **FLIP DISTANCE OF POINT-SET TRIANGULATIONS is NP-complete.** Source: Lubiw and Pathak
(2015), Theorem 2; Pilz (2014), point sets in general position. -/
public theorem_wanted flipDistancePointSetTriangulation_npComplete :
    flipDistancePointSetTriangulationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L flipDistancePointSetTriangulationDec

end MetaMathlibExt.Complexity.NPComplete.FlipDistancePointSetTriangulation
