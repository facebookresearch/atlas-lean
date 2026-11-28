/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHINESE POSTMAN FOR MIXED GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND25] CHINESE POSTMAN FOR MIXED
GRAPHS;
C. H. Papadimitriou, "On the complexity of edge traversing", Journal of the ACM 23 (1976),
544-554, doi:10.1145/321958.321974.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChinesePostmanMixedGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphs

/-!
# CHINESE POSTMAN FOR MIXED GRAPHS is NP-complete

Given a mixed graph `G = (V, A, E)`, where `A` is a set of directed edges and `E` a set of
undirected edges on `V`, a length `l(e) ∈ Z₀⁺` for each `e ∈ A ∪ E`, and a bound `B ∈ Z⁺`,
is there a cycle in `G` that includes each directed and undirected edge at least once,
traversing directed edges only in the specified direction, and that has total length no
more than `B`?

The vertices are `0, ..., n - 1`. A directed edge is a triple `(u, v, l)` (from `u` to `v`,
length `l`), an undirected edge a triple `(u, v, l)` (joining `u` and `v`); neither list has
loops or repeated edges. A cycle is a closed walk, given as a list of steps: `(true, j, _)`
traverses directed edge `j` from its tail to its head, `(false, j, true)` traverses
undirected edge `j = (u, v, l)` from `u` to `v`, and `(false, j, false)` from `v` to `u`.
Consecutive steps meet, the last step ends where the first begins, and edges may be
traversed several times; its length is the sum of the lengths of its steps.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CHINESE POSTMAN FOR MIXED GRAPHS is NP-complete.** Source: Garey and Johnson
(1979), [ND25]; Papadimitriou (1976). -/
public theorem_wanted chinesePostmanMixedGraphs_npComplete :
    chinesePostmanMixedGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chinesePostmanMixedGraphsDec

end MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphs
