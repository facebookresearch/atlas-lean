/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PURE-k-DIR GRAPH RECOGNITION is NP-complete for every fixed k ≥ 2

Source:
J. Kratochvíl and J. Matoušek, "NP-hardness results for intersection graphs",
Commentationes Mathematicae Universitatis Carolinae 30 (1989), no. 4, 761-773,
http://dml.cz/dmlcz/106799 (Section 2 definitions, Theorem 1 and Proposition 5);
J. Kratochvíl, "A special planar satisfiability problem and a consequence of its
NP-completeness", Discrete Applied Mathematics 52 (1994), 233-252,
doi:10.1016/0166-218X(94)90143-0 (the case `k = 2`);
J. Kratochvíl and J. Matoušek, "Intersection graphs of segments", Journal of Combinatorial
Theory, Series B 62 (1994), 289-315, doi:10.1006/jctb.1994.1071 (membership in NP);
ISGCI, *Information System on Graph Classes and their Inclusions*, classes PURE-2-DIR
(gc_867) and PURE-3-DIR (gc_868), problem Recognition: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PureKDirGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PureKDirGraphRecognition

open KDirGraphRecognition (KDirGraphRecognitionInstance Graph WellFormed)

/-!
# PURE-k-DIR GRAPH RECOGNITION is NP-complete for every fixed k ≥ 2

Fix an integer `k ≥ 2`.
INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` a PURE-`k`-DIR graph, that is, the intersection graph of straight line segments
in the plane whose slopes lie among at most `k` real numbers, such that no two segments of the
same direction intersect?

Kratochvíl and Matoušek (1989), Section 2: "PURE-k-DIR(d₁, …, d_k) = k-DIR(d₁, …, d_k)|(no two
segments of the same direction intersect each other), PURE-k-DIR = ⋃{PURE-k-DIR(d₁, …, d_k);
d₁, …, d_k real numbers}", where `k-DIR(d₁, …, d_k)` is the class of intersection graphs of
segments with slopes among `d₁, …, d_k` and `IG(C)|R` the graphs of `IG(C)` having a
representation satisfying the restriction `R`. Their Theorem 1 states that RECOG(PURE-k-DIR) is
NP-complete for every `k ≥ 2` (Proposition 5; the case `k = 2` is proved in detail in
Kratochvíl (1994)), and their remark after it attributes membership in NP, for every fixed `k`,
to Kratochvíl and Matoušek (1994). ISGCI's definition of PURE-2-DIR and PURE-3-DIR: "the
intersection graph of straight line segments lying in at most 2 [3] directions in the plane,
with the additional condition that any two parallel segments are disjoint."

`IsPureKDirGraph k H` is the representation of `KDirGraphRecognition.IsKDirGraph k H` (slopes
`s : Fin k → ℝ`, not necessarily distinct; for each vertex `v` a slope index `c v` and the
closed segment `SimpleGraph.Segment (a v) (b v)` with `(a v).1 < (b v).1` and
`(b v).2 - (a v).2 = s (c v) * ((b v).1 - (a v).1)`; two distinct vertices adjacent exactly when
their segments share a point) with the restriction added: two distinct vertices whose segments
have the same slope have disjoint segments. Segments of one direction are those of one slope
value, so the restriction compares `s (c u)` with `s (c v)` rather than the indices. Taking
slopes, i.e. non-vertical segments, loses nothing: the class is a union over all slope tuples,
and a rotation makes any `k` directions non-vertical. The instance (vertex count and edge list),
the graph (`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and `WellFormed` (a simple edge list)
are those of `WantedExt.Complexity.NPComplete.KDirGraphRecognitionWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PURE-k-DIR GRAPH RECOGNITION is NP-complete for every fixed `k ≥ 2`.** Source:
Kratochvíl and Matoušek (1989), Theorem 1; Kratochvíl (1994) for `k = 2`; membership in NP:
Kratochvíl and Matoušek (1994). -/
public theorem_wanted pureKDirGraphRecognition_npComplete (k : ℕ) (hk : 2 ≤ k) :
    pureKDirGraphRecognitionDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (pureKDirGraphRecognitionDec k)

end MetaMathlibExt.Complexity.NPComplete.PureKDirGraphRecognition
