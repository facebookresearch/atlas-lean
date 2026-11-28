/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL MORSE MATCHING is NP-complete

Source:
M. Joswig and M. E. Pfetsch, "Computing optimal Morse matchings", SIAM Journal on Discrete
Mathematics 20 (2006), 11-25, doi:10.1137/S0895480104445885 (arXiv:math/0408331), Section 4;
Ö. Eğecioğlu and T. F. Gonzalez, "A computationally intractable problem on simplicial
complexes", Computational Geometry 6 (1996), 85-98, doi:10.1016/0925-7721(95)00015-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OptimalMorseMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalMorseMatching

/-!
# OPTIMAL MORSE MATCHING is NP-complete

INSTANCE: a finite simplicial complex `Δ` (its nonempty faces) and a nonnegative integer `c`.
QUESTION: is there a Morse matching of `Δ` with at most `c` critical faces?

Following Joswig and Pfetsch (Section 2), the empty face is ignored; for faces `F, G` write
`F ≺ G` when `F ⊂ G` and `|G| = |F| + 1`. The Hasse diagram has an arc `G → F` for every
`F ≺ G`. A matching `M` is a set of such pairs, each face in at most one pair; `M` is a Morse
matching when the Hasse diagram with the arcs of `M` reversed has no directed cycle, and the
faces in no pair of `M` are critical. Joswig and Pfetsch show that maximizing a Morse matching,
equivalently minimizing the number of critical faces, is NP-hard, already for connected pure
2-dimensional complexes embeddable in `ℝ³`, via the collapsibility problem of Eğecioğlu and
Gonzalez.

The vertices are natural numbers; the complex is the list of its nonempty faces, each a strictly
increasing list of vertices, no face listed twice, and closed under taking nonempty subsets (for
increasing lists, the nonempty sublists). All faces are listed, as the paper measures the input
by its face lattice. A finite directed graph has no directed cycle iff some ranking of its vertices
strictly decreases along every arc, so acyclicity is stated by a ranking `r`: `r F < r G` for an
unmatched pair `F ≺ G` (arc `G → F`), and `r G < r F` for a matched one (arc `F → G`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **OPTIMAL MORSE MATCHING is NP-complete.** Source: Joswig and Pfetsch (2006), Section 4;
Eğecioğlu and Gonzalez (1996). -/
public theorem_wanted optimalMorseMatching_npComplete :
    optimalMorseMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimalMorseMatchingDec

end MetaMathlibExt.Complexity.NPComplete.OptimalMorseMatching
