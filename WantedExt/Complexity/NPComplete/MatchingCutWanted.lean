/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATCHING CUT is NP-complete

Source:
V. Chvátal, "Recognizing decomposable graphs", Journal of Graph Theory 8(1) (1984), 51-53,
doi:10.1002/jgt.3190080106 (recognizing decomposable graphs is NP-complete, already for graphs
of maximum degree 4).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MatchingCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatchingCut

/-!
# MATCHING CUT is NP-complete

INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` decomposable, that is, can its vertices be colored red and blue so that each
color appears on at least one vertex and each vertex `v` has at most one neighbor with a color
different from that of `v`?

Equivalently, `G` has a matching cut: a partition of `V` into two nonempty parts (the color
classes) whose crossing edges are pairwise disjoint, since a vertex with two neighbors on the
other side would meet two crossing edges. A coloring is a function `Fin n → Bool`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MATCHING CUT is NP-complete.** Source: Chvátal (1984). -/
public theorem_wanted matchingCut_npComplete :
    matchingCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L matchingCutDec

end MetaMathlibExt.Complexity.NPComplete.MatchingCut
