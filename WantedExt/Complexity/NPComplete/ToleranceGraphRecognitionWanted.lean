/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOLERANCE GRAPH RECOGNITION is NP-complete

Source:
G. B. Mertzios, I. Sau and S. Zaks, "The recognition of tolerance and bounded tolerance graphs",
SIAM Journal on Computing 40 (2011), 1234-1257, doi:10.1137/090780328 (arXiv:1001.3251;
Section 1: the definition of tolerance graphs used below, and "both recognition problems are
NP-complete", membership in NP citing Hayward and Shamir).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ToleranceGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ToleranceGraphRecognition

/-!
# TOLERANCE GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a tolerance graph?

Mertzios, Sau and Zaks (Section 1): "A simple undirected graph `G = (V, E)` on `n` vertices is a
tolerance graph if there exists a collection `I = {I_i | i = 1, 2, …, n}` of closed intervals on
the real line and a set `t = {t_i | i = 1, 2, …, n}` of positive numbers, such that for any two
vertices `v_i, v_j ∈ V`, `v_i v_j ∈ E` if and only if `|I_i ∩ I_j| ≥ min{t_i, t_j}`." Here
`|I|` is the length of an interval; they prove the recognition problem NP-complete.

The graph is given by an edge list on `Fin n`. Vertex `v` gets the closed interval
`[l v, r v]` with `l v ≤ r v` and the tolerance `t v > 0`, all real. The length of the
intersection of `[a, b]` and `[c, d]` is `max 0 (min b d - max a c)` (`overlap`), which is `0`
for disjoint intervals. The condition is required for distinct vertices (the graph has no
loops). Isolated vertices do not change the answer (an interval far from all others), so the
binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TOLERANCE GRAPH RECOGNITION is NP-complete.** Source: Mertzios, Sau and Zaks (2011). -/
public theorem_wanted toleranceGraphRecognition_npComplete :
    toleranceGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L toleranceGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.ToleranceGraphRecognition
