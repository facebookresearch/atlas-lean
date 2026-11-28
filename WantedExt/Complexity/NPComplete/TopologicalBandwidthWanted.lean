/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOPOLOGICAL BANDWIDTH is NP-complete

Source:
F. S. Makedon, C. H. Papadimitriou and I. H. Sudborough, "Topological bandwidth", SIAM Journal
on Algebraic and Discrete Methods 6 (1985), 418-444, doi:10.1137/0606044 (conference version:
CAAP '83, Lecture Notes in Computer Science (1983), 317-331, doi:10.1007/3-540-12727-5_19);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (the underlying measure).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TopologicalBandwidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TopologicalBandwidth

open MetaMathlibExt.Complexity.NPComplete.Bandwidth (BandwidthInstance)

/-!
# TOPOLOGICAL BANDWIDTH is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` and a positive integer `K`.
QUESTION: is the topological bandwidth of `G` at most `K`, that is, is there a graph `G'`
obtained from `G` by subdividing some of its edges with some number (possibly zero) of
degree-two vertices whose bandwidth is at most `K`?

Makedon, Papadimitriou and Sudborough define the topological bandwidth `tb(G)` as the minimum
bandwidth of all graphs obtained from `G` by subdividing some of `G`'s edges with some number
(possibly zero) of degree-two vertices (the homeomorphic images of `G`), and prove that the
Topological Bandwidth problem is NP-complete, even for graphs of maximum degree three.

The subdivided graph is built explicitly (`subdivide`): for subdivision counts `s` (one per
edge, in edge-list order), the `k`-th edge `(a, b)` with `s[k] = m` is replaced by the path
`a, v₁, …, vₘ, b` through `m` fresh vertices, numbered consecutively after the original `n`
vertices and the fresh vertices of the earlier edges (`m = 0` keeps the edge `(a, b)`). The
bandwidth of the subdivided graph is the BANDWIDTH predicate of `BandwidthWanted`, reused
unchanged: a bijective labelling of the vertices by `0, …, n' - 1` in which the endpoints of
every edge get labels at most `K` apart.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TOPOLOGICAL BANDWIDTH is NP-complete.** Source: Makedon, Papadimitriou and Sudborough
(1985). -/
public theorem_wanted topologicalBandwidth_npComplete :
    topologicalBandwidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L topologicalBandwidthDec

end MetaMathlibExt.Complexity.NPComplete.TopologicalBandwidth
