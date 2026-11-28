/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on co-bipartite graphs is NP-complete

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Nordic Journal
of Computing 7 (2000), 14-31 (STACS 1994, LNCS 775, 769-780, doi:10.1007/3-540-57785-8_189);
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70 (2023), 307-322, doi:10.1007/s00454-022-00472-y (records
"Max Cut remains NP-hard even for ... co-bipartite graphs [Bodlaender and Jansen]");
ISGCI, class "co-bipartite" (gc_486), problem Maximum cut, NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SimpleMaxCutCoBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCoBipartite

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT on co-bipartite graphs is NP-complete

INSTANCE: a co-bipartite graph `G = (V, E)` (the complement of a bipartite graph) and a positive
integer `K`.
QUESTION: is there a partition of `V` into sets `A`, `B` such that at least `K` edges have one
endpoint in `A` and the other in `B`?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one) restricted to co-bipartite graphs,
which Bodlaender and Jansen prove NP-complete. The instance, the simple-edge-list conditions and
the question are those of MAXIMUM CUT (`CSLibExt.Complexity.NPComplete.MaxCutDefs`, whose
question counts edges), reused as in `SimpleMaxCutDegreeThreeWanted`; the restriction adds to
`WellFormed` that the complement of `Cslib.Complexity.Karp.edgeGraph` is bipartite (Mathlib's
`SimpleGraph.IsBipartite`, as in `TreewidthCoBipartiteWanted`), i.e. the vertices split into two
cliques, and `0 < K`. A co-bipartite graph has a clique on at least `⌈|V| / 2⌉` vertices, so
its edge list has at least `C(⌈|V| / 2⌉, 2)` entries and the binary vertex count does not make
the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SIMPLE MAX CUT on co-bipartite graphs is NP-complete.** Source: Bodlaender and Jansen
(2000); ISGCI (gc_486). -/
public theorem_wanted simpleMaxCutCoBipartite_npComplete :
    simpleMaxCutCoBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutCoBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCoBipartite
