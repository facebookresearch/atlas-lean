/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY of circular-arc graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (comment:
NP-complete for circular arc graphs, even given their representation as families of arcs);
M. R. Garey, D. S. Johnson, G. L. Miller and C. H. Papadimitriou, "The complexity of coloring
circular arcs and chords", SIAM Journal on Algebraic and Discrete Methods 1(2) (1980), 216-227,
doi:10.1137/0601025.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CircularArcColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularArcColoring

/-!
# GRAPH K-COLORABILITY of circular-arc graphs is NP-complete

An instance is a finite family of arcs on a circle, which represents its intersection graph
(one vertex per arc, two vertices adjacent when their arcs meet), and a positive integer
`K ≤ |V|`. The question is whether the intersection graph is `K`-colorable: can the arcs be
colored with `K` colors so that intersecting arcs get different colors? Garey, Johnson, Miller
and Papadimitriou (1980) proved this NP-complete; for each fixed `K` it is polynomial.

Arcs are closed and their endpoints are among `L` points `0, …, L - 1` placed in clockwise
order on the circle; every finite family of closed arcs can be put in this form without
changing which arcs meet, by numbering the distinct endpoints in clockwise order. The arc
`(a, b)` runs clockwise from `a` to `b`: it contains the points `a, a + 1, …, b` when `a ≤ b`,
and wraps through `L - 1` and `0` when `b < a`. Two closed arcs with endpoints among the points
meet if and only if they share one of the points. The family is a list, so two vertices may
carry the same arc.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH K-COLORABILITY of circular-arc graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT4]; Garey, Johnson, Miller and Papadimitriou (1980). -/
public theorem_wanted circularArcColoring_npComplete :
    circularArcColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circularArcColoringDec

end MetaMathlibExt.Complexity.NPComplete.CircularArcColoring
