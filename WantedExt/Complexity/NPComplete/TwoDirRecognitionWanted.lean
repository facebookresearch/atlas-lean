/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF 2-DIR GRAPHS is NP-complete

Source:
J. Kratochvíl and J. Matoušek, "NP-hardness results for intersection graphs", Commentationes
Mathematicae Universitatis Carolinae 30 (1989), 761-773, http://dml.cz/dmlcz/106799 (Theorem 1:
"RECOG(k-DIR) and RECOG(PURE-k-DIR), for every k ≥ 2, are NP-complete"; Proposition 5, whose
proof for 2-DIR is deferred to the next reference);
J. Kratochvíl, "A special planar satisfiability problem and a consequence of its
NP-completeness", Discrete Applied Mathematics 52 (1994), 233-252,
doi:10.1016/0166-218X(94)90143-0;
ISGCI, *Information System on Graph Classes and their Inclusions*, class "2-DIR" (gc_864),
problem Recognition: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoDirRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDirRecognition

open SegmentIntersectionClique (Seg toPoint segPoints)

/-!
# RECOGNITION OF 2-DIR GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` a 2-DIR graph, i.e. the intersection graph of straight line segments lying in at
most 2 directions in the plane (one segment per vertex, two distinct vertices adjacent exactly when
their segments share a point)?

Representation. A segment is a closed segment `segPoints σ` between two distinct points with
integer coordinates (the encoding of `SegmentIntersectionCliqueWanted`, reused here), and the two
directions are the horizontal and the vertical one. Neither restriction changes the class: an
invertible linear map of the plane sends any two directions to the two coordinate axes and
preserves segments and their intersections (a single direction is a special case), and two
axis-parallel segments meet exactly when certain coordinates compare as `≤` or `=`, so replacing
the finitely many x-coordinates, and separately the y-coordinates, by their ranks preserves every
intersection and non-intersection and keeps every segment non-degenerate. Segments of different
vertices may coincide.

Kratochvíl and Matoušek (1989) state that recognizing `k`-DIR graphs is NP-complete for every
`k ≥ 2`; the proof for 2-DIR graphs is given in Kratochvíl (1994). Membership in NP holds for
this encoding, where the vertex count is a binary number: isolated vertices can always be added to
a representation of the other vertices as pairwise disjoint horizontal segments at new heights
above all other segments, so `G` is 2-DIR exactly when its vertices incident to an edge (at most
twice the length of the edge list) are; a certificate is a representation of those vertices, and
by the rank argument above its coordinates can be taken at most four times the length of the edge
list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECOGNITION OF 2-DIR GRAPHS is NP-complete.** Source: Kratochvíl and Matoušek (1989),
Theorem 1; Kratochvíl (1994); ISGCI, class "2-DIR". -/
public theorem_wanted twoDirRecognition_npComplete :
    twoDirRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoDirRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.TwoDirRecognition
