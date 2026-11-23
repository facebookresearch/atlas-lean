/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET in segment intersection graphs is NP-complete

Source:
J. Kratochvíl and J. Nešetřil, "INDEPENDENT SET and CLIQUE problems in intersection-defined
classes of graphs", Commentationes Mathematicae Universitatis Carolinae 31(1) (1990), 85-93,
http://dml.cz/dmlcz/106821 (Theorem 1);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SegmentIntersectionCliqueWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetSegmentIntersection

open SegmentIntersectionClique (SegmentIntersectionCliqueInstance Graph)

/-!
# INDEPENDENT SET in segment intersection graphs is NP-complete

INSTANCE: a finite set of straight line segments in the plane, each given by the integer
coordinates of its two (distinct) endpoints, and a positive integer `K` at most the number of
segments.

QUESTION: does the intersection graph of the segments (one vertex per segment, two segments
adjacent when they share a point) contain an independent set of size `K` or more, that is, are
there `K` pairwise disjoint segments?

This is Garey and Johnson's [GT20] INDEPENDENT SET restricted to SEG graphs, the intersection
graphs of straight line segments in the plane. Kratochvíl and Nešetřil (1990), Theorem 1:
"INDEPENDENT SET is polynomially solvable in 1-DIR and PURE-2-DIR, but it is NP-complete when
restricted to 2-DIR and PURE-3-DIR", where `k`-DIR is the class of intersection graphs of
segments lying in at most `k` directions; both classes are contained in SEG. Their reduction,
from INDEPENDENT SET on planar graphs of maximum degree four, builds the segments from a grid
embedding of linear size (vertices become short horizontal segments, edge pieces become grid
segments, slightly shortened and shifted), so the segments have integer endpoints of polynomial
size after scaling; Section 3 of the paper describes SEG representations in exactly this form,
by the integer coordinates of the endpoints. As in `SegmentIntersectionCliqueWanted`, the graph
is given by its segments: recognizing SEG graphs is NP-hard (Kratochvíl and Nešetřil, Remark),
and some SEG graphs need exponentially large coordinates. Membership in NP: `K` pairwise
disjoint segments are a certificate, and whether two segments with integer endpoints meet is
decided by exact orientation tests.

The instance, the segments, their intersection graph and the well-formedness conditions are
those of `SegmentIntersectionCliqueWanted`, used as is: `SegmentIntersectionClique.Graph` (the
closed segment `SimpleGraph.Segment a b` between the endpoints, so segments that touch at an
endpoint intersect; one vertex per list entry) and `SegmentIntersectionClique.WellFormed`
(distinct endpoints, segments pairwise distinct as point sets, `0 < K ≤` the number of
segments). Independence is Mathlib's `SimpleGraph.IsIndepSet`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The intersection graph of the segments has an independent set of size `K` or more. -/
def IndependentSetSegmentIntersectionFeasible (i : SegmentIntersectionCliqueInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), i.2 ≤ S.card ∧ (Graph i).IsIndepSet (S : Set (Fin i.1.length))

open Classical in
/-- INDEPENDENT SET in segment intersection graphs as a decision problem over bitstrings. -/
noncomputable def independentSetSegmentIntersectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SegmentIntersectionCliqueInstance) x with
  | some i => decide (SegmentIntersectionClique.WellFormed i ∧
      IndependentSetSegmentIntersectionFeasible i)
  | none => false

/-- **INDEPENDENT SET in segment intersection graphs is NP-complete.** Source: Kratochvíl and
Nešetřil (1990), Theorem 1; Garey and Johnson (1979), [GT20]. -/
public theorem_wanted independentSetSegmentIntersection_npComplete :
    independentSetSegmentIntersectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetSegmentIntersectionDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetSegmentIntersection
