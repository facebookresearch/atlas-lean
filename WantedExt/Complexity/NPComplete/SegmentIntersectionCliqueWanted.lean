/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE in segment intersection graphs (SEG) is NP-complete

Source:
S. Cabello, J. Cardinal and S. Langerman, "The clique problem in ray intersection graphs",
Discrete & Computational Geometry 50 (2013), 771-783, doi:10.1007/s00454-013-9538-5
(arXiv:1111.5986);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE;
ISGCI (https://www.graphclasses.org/classes/gc_862.html), problem "Clique" on SEG graphs:
NP-complete, with the attribution to Cabello, Cardinal and Langerman.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import WantedExt.Complexity.NPComplete.RayIntersectionCliqueWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SegmentIntersectionClique

open RayIntersectionClique (toInt)

/-!
# CLIQUE in segment intersection graphs (SEG) is NP-complete

INSTANCE: a finite set of straight line segments in the plane, each given by the integer
coordinates of its two (distinct) endpoints, and a positive integer `K` at most the number of
segments. QUESTION: does the intersection graph of the segments (one vertex per segment, two
segments adjacent when they share a point) contain a clique of size `K` or more?

This is Garey and Johnson's [GT19] CLIQUE restricted to SEG graphs, the intersection graphs of
straight line segments in the plane (ISGCI class `gc_862`), with the graph given by a geometric
representation, as in `RayIntersectionCliqueWanted` (CLIQUE in ray intersection graphs, whose
integer encoding `toInt` is reused). Recognizing SEG graphs from the graph alone is not known to
be in NP, so the segments are part of the input. Cabello, Cardinal and Langerman (2013) prove
maximum clique NP-hard in ray intersection graphs, which, as their abstract states, implies
NP-hardness for segment intersection graphs; their Lemma 2.8 builds the rays with integer
coordinates in polynomial time. Since their rays are open (origin excluded), scaling every
coordinate by a large enough integer, starting each ray one direction step past its origin and
cutting it at a far integer point keeps every intersection point and adds none, giving integer
segments with the same intersection graph. Membership in NP is the certificate argument: `K`
pairwise intersecting segments are a certificate, and whether two segments with integer endpoints
meet is decided by exact orientation tests.

A segment is the closed segment `SimpleGraph.Segment a b` (`MathlibExt`'s straight-line segment
in `ℝ × ℝ`) between its endpoints `a ≠ b`, so segments that touch at an endpoint intersect. The
family is a set of segments, given as a list whose entries are pairwise distinct as point sets;
one vertex per entry. Integers are encoded as pairs `(p, q)` of naturals standing for `p - q`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A point with integer coordinates `(x, y)`, each encoded as a pair of naturals. -/
abbrev IntPoint := (ℕ × ℕ) × (ℕ × ℕ)

/-- A segment, given by its two endpoints. -/
abbrev Seg := IntPoint × IntPoint

/-- An instance: the segments and the bound `K`. -/
abbrev SegmentIntersectionCliqueInstance := List Seg × ℕ

/-- The point of the real plane with the encoded integer coordinates. -/
def toPoint (p : IntPoint) : ℝ × ℝ := ((toInt p.1 : ℝ), (toInt p.2 : ℝ))

/-- The point set of a segment: the closed segment between its endpoints. -/
def segPoints (σ : Seg) : Set (ℝ × ℝ) :=
  SimpleGraph.Segment (toPoint σ.1) (toPoint σ.2)

/-- The intersection graph of the segments: one vertex per list entry, two distinct entries
adjacent when their segments share a point. -/
def Graph (i : SegmentIntersectionCliqueInstance) : SimpleGraph (Fin i.1.length) :=
  SimpleGraph.fromRel fun a b => (segPoints (i.1.get a) ∩ segPoints (i.1.get b)).Nonempty

/-- Well-formedness of an instance: every segment has distinct endpoints, the segments are
pairwise distinct as point sets (a set of segments), and `0 < K ≤` the number of segments. -/
def WellFormed (i : SegmentIntersectionCliqueInstance) : Prop :=
  (∀ σ ∈ i.1, toPoint σ.1 ≠ toPoint σ.2) ∧ (i.1.map segPoints).Nodup ∧ 0 < i.2 ∧
    i.2 ≤ i.1.length

/-- The intersection graph has a clique of size `K` or more. -/
def SegmentIntersectionCliqueFeasible (i : SegmentIntersectionCliqueInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), i.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1.length))

open Classical in
/-- CLIQUE in segment intersection graphs as a decision problem over bitstrings. -/
noncomputable def segmentIntersectionCliqueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SegmentIntersectionCliqueInstance) x with
  | some i => decide (WellFormed i ∧ SegmentIntersectionCliqueFeasible i)
  | none => false

/-- **CLIQUE in segment intersection graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT19]; NP-hardness: Cabello, Cardinal and Langerman (2013); membership: a clique is a
polynomial-time checkable certificate. -/
public theorem_wanted segmentIntersectionClique_npComplete :
    segmentIntersectionCliqueDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L segmentIntersectionCliqueDec

end MetaMathlibExt.Complexity.NPComplete.SegmentIntersectionClique
