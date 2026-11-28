/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BICONNECTIVITY AUGMENTATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND18] BICONNECTIVITY AUGMENTATION;
K. P. Eswaran and R. E. Tarjan, "Augmentation problems", SIAM Journal on Computing 5 (1976),
653-665, doi:10.1137/0205044.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BiconnectivityAugmentationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BiconnectivityAugmentation

/-!
# BICONNECTIVITY AUGMENTATION is NP-complete

Given a graph `G = (V, E)`, a weight `w({u, v}) ∈ Z⁺` for each unordered pair `{u, v}` of
vertices from `V`, and a positive integer `B`, is there a set `E'` of unordered pairs of
vertices from `V` such that `∑_{e ∈ E'} w(e) ≤ B` and the graph `G' = (V, E ∪ E')` is
biconnected, i.e., cannot be disconnected by removing a single vertex?

The vertices are `0, ..., n - 1` with `n ≥ 3`; biconnectivity is
`SimpleGraph.IsVertexConnected 2` (`MathlibExt`): more than two vertices, connected, and
connected after deleting any one vertex. The weights are an `n × n` symmetric matrix whose
off-diagonal entries are positive (the diagonal is never used). `E'` is a list of pairs of
distinct vertices; listing a pair twice only adds its weight twice.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BICONNECTIVITY AUGMENTATION is NP-complete.** Source: Garey and Johnson (1979),
[ND18]; Eswaran and Tarjan (1976). -/
public theorem_wanted biconnectivityAugmentation_npComplete :
    biconnectivityAugmentationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L biconnectivityAugmentationDec

end MetaMathlibExt.Complexity.NPComplete.BiconnectivityAugmentation
