/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH 3-COLORABILITY of segment intersection graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY, comment:
"Also remains NP-complete for K = 3 if G is an intersection graph for straight line segments in
the plane [Ehrlich, Even, and Tarjan, 1976]";
G. Ehrlich, S. Even and R. E. Tarjan, "Intersection graphs of curves in the plane", Journal of
Combinatorial Theory, Series B 21(1) (1976), 8-20, doi:10.1016/0095-8956(76)90022-8;
P. Ossona de Mendez, "3-colorability and contacts of segments", Série du CAMS 171 (1999), 1-2,
HAL hal-00008547 (Theorem 1: NP-complete even for contact graphs of segments in 4 directions,
from the grid T-shape contact representation of planar graphs of H. de Fraysseix, P. Ossona de
Mendez and P. Rosenstiehl, "On triangle contact graphs", Combinatorics, Probability and Computing
3 (1994), 233-246, doi:10.1017/S0963548300001139).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SegmentIntersectionCliqueWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilitySegmentIntersection

open SegmentIntersectionClique (Seg toPoint segPoints)

/-!
# GRAPH 3-COLORABILITY of segment intersection graphs is NP-complete

INSTANCE: a finite set of straight line segments in the plane, each given by the integer
coordinates of its two (distinct) endpoints.
QUESTION: is the intersection graph of the segments (one vertex per segment, two segments adjacent
when they share a point) `3`-colorable?

This is GRAPH K-COLORABILITY ([GT4], `GraphColoringWanted`) with `K = 3`, restricted to
intersection graphs of straight line segments in the plane, as recorded by Garey and Johnson with
the attribution to Ehrlich, Even and Tarjan, whose abstract states that "for every k ≥ 3, the
problem of determining whether an intersection graph of straight line-segments is k-colorable is
NP-complete". As in `SegmentIntersectionCliqueWanted`, the graph is given by its segments:
recognizing segment intersection graphs from the graph alone is not known to be in NP. Ossona de
Mendez gives a reduction from 3-colorability of planar graphs whose output is a family of
segments in four directions obtained from a grid (T-shape) contact representation, so the
segments have integer coordinates of polynomial size; this is the form taken here. Membership in
NP: a colouring is a certificate, and whether two segments with integer endpoints meet is decided
by exact orientation tests.

The segments, their point sets and the intersection graph are those of
`SegmentIntersectionCliqueWanted` (`SegmentIntersectionClique.segPoints`, the closed segment
between the endpoints, and `SegmentIntersectionClique.Graph`, whose bound component plays no role
in the graph). Well-formedness is the sibling's without the bound: distinct endpoints, and
segments pairwise distinct as point sets. `3`-colorability is Mathlib's `SimpleGraph.Colorable`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the list of segments. -/
abbrev ThreeColorabilitySegmentIntersectionInstance := List Seg

/-- The intersection graph of the segments: `SegmentIntersectionClique.Graph`, whose bound
component (here `0`) does not affect the graph. -/
def Graph (i : ThreeColorabilitySegmentIntersectionInstance) : SimpleGraph (Fin i.length) :=
  SegmentIntersectionClique.Graph (i, 0)

/-- Well-formedness of an instance: every segment has distinct endpoints, and the segments are
pairwise distinct as point sets. -/
def WellFormed (i : ThreeColorabilitySegmentIntersectionInstance) : Prop :=
  (∀ σ ∈ i, toPoint σ.1 ≠ toPoint σ.2) ∧ (i.map segPoints).Nodup

/-- The intersection graph of the segments is `3`-colorable. -/
def ThreeColorabilitySegmentIntersectionFeasible
    (i : ThreeColorabilitySegmentIntersectionInstance) : Prop :=
  (Graph i).Colorable 3

open Classical in
/-- GRAPH 3-COLORABILITY of segment intersection graphs as a decision problem over bitstrings. -/
noncomputable def threeColorabilitySegmentIntersectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeColorabilitySegmentIntersectionInstance) x with
  | some i => decide (WellFormed i ∧ ThreeColorabilitySegmentIntersectionFeasible i)
  | none => false

/-- **GRAPH 3-COLORABILITY of segment intersection graphs is NP-complete.** Source: Garey and
Johnson (1979), [GT4]; Ehrlich, Even and Tarjan (1976); Ossona de Mendez (1999). -/
public theorem_wanted threeColorabilitySegmentIntersection_npComplete :
    threeColorabilitySegmentIntersectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilitySegmentIntersectionDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilitySegmentIntersection
