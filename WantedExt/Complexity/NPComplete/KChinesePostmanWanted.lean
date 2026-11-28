/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-CHINESE POSTMAN is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MINIMUM K-CHINESE POSTMAN PROBLEM;
G. N. Frederickson, M. S. Hecht and C. E. Kim, "Approximation algorithms for some routing
problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017 (the k-person
minimax Chinese postman problem, among the NP-complete routing problems treated there).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KChinesePostmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KChinesePostman

open ChinesePostmanMixedGraphs (ChinesePostmanMixedGraphsInstance Step stepEnds stepLength)

/-!
# k-CHINESE POSTMAN is NP-complete

INSTANCE: a multigraph `G = (V, E)`, an initial vertex `s ∈ V`, a length `l(e) ∈ ℕ` for each
`e ∈ E`, a positive integer `k`, and a positive integer `K`. QUESTION: is there a collection of
`k` cycles, each containing `s`, that together traverse every edge of `G` at least once, such
that the longest of the `k` cycles has length at most `K`?

This is the decision version of MINIMUM K-CHINESE POSTMAN PROBLEM in the compendium of Crescenzi
and Kann, whose measure is the maximum length of the `k` cycles.

The vertices are `0, …, n - 1` and the edges are a list of triples `(u, v, l)` (joining `u` and
`v`, length `l`); repeated triples are parallel edges and `(v, v, l)` is a loop. As in postman
problems, a cycle is a closed walk from `s`, which may repeat vertices and edges, and its length
counts every traversal. Walks reuse the steps of `ChinesePostmanMixedGraphsWanted`, reading the
multigraph as a mixed graph without directed edges: the step `(false, j, true)` traverses edge
`j = (u, v, l)` from `u` to `v`, and `(false, j, false)` from `v` to `u`. Consecutive steps
meet, the first step starts at `s` and the last ends at `s`; the empty walk (staying at `s`, of
length `0`) is allowed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **k-CHINESE POSTMAN is NP-complete.** Source: Crescenzi and Kann, MINIMUM K-CHINESE POSTMAN
PROBLEM; Frederickson, Hecht and Kim (1978). -/
public theorem_wanted kChinesePostman_npComplete :
    kChinesePostmanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kChinesePostmanDec

end MetaMathlibExt.Complexity.NPComplete.KChinesePostman
