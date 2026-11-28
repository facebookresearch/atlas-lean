/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE in ray intersection graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE;
S. Cabello, J. Cardinal and S. Langerman, "The clique problem in ray intersection graphs",
Discrete & Computational Geometry 50(3) (2013), 771-783, doi:10.1007/s00454-013-9538-5
(arXiv:1111.5986), Lemma 2.8 and Theorem 2.10.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RayIntersectionCliqueDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RayIntersectionClique

/-!
# CLIQUE in ray intersection graphs is NP-complete

INSTANCE: a finite set of rays (half-lines) in the plane, each given by integer
coordinates, and a positive integer `K` at most the number of rays. QUESTION: does the
intersection graph of the rays (one vertex per ray, two rays adjacent when they share a point)
contain a clique of size `K` or more, i.e. are there `K` rays that pairwise intersect?

This is Garey and Johnson's [GT19] CLIQUE (INSTANCE: "Graph `G = (V, E)`, positive integer
`K ≤ |V|`." QUESTION: "Does `G` contain a clique of size `K` or more, i.e., a subset `V' ⊆ V`
with `|V'| ≥ K` such that every two vertices in `V'` are joined by an edge in `E`?") restricted
to ray intersection graphs, with the graph given by a geometric representation. Cabello,
Cardinal and Langerman (2013), Theorem 2.10: "Finding a maximum clique in a ray intersection
graph is NP-hard, even when the input is given by a geometric representation as a set of
rays"; their Lemma 2.8 constructs the rays "described with integer coordinates" in polynomial
time. Membership in NP is not stated there; it is the standard certificate argument: `K`
pairwise intersecting rays are a certificate, and whether two rays with integer data meet is
decided by exact rational arithmetic on a `2 × 2` linear system.

A ray is given by its origin `(x, y)` and a nonzero direction `(d, e)`, all integers, each
encoded as a pair `(p, q)` of naturals standing for `p - q`. As in the source ("we use ray to
refer to an open ray, that is, a ray does not contain its origin", Section 1), a ray is the
point set `{(x + t d, y + t e) : t ∈ ℝ, t > 0}` of `ℝ × ℝ`. The family is a set of rays, given
as a list whose entries are pairwise distinct as point sets (two encodings of one ray, such as
directions `(1, 0)` and `(2, 0)` from the same origin, may not both occur); one vertex per
entry.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLIQUE in ray intersection graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT19]; NP-hardness, with the rays given by integer coordinates: Cabello, Cardinal and
Langerman (2013), Lemma 2.8 and Theorem 2.10; membership: a clique is a polynomial-time
checkable certificate. -/
public theorem_wanted rayIntersectionClique_npComplete :
    rayIntersectionCliqueDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rayIntersectionCliqueDec

end MetaMathlibExt.Complexity.NPComplete.RayIntersectionClique
