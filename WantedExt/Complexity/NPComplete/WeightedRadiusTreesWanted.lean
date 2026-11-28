/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED RADIUS for trees is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER (p. 205),
comments "NP-complete in the strong sense, even if G is a tree. The variant in which 'diameter'
is replaced by 'radius' has the same complexity" (credited there to Perl and Zaks, 1978);
Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer
Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeightedRadiusTreesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedRadiusTrees

open MetaMathlibExt.Complexity.NPComplete.WeightedDiameter
  (WeightedDiameterInstance Graph weightedLength)

/-!
# WEIGHTED RADIUS for trees is NP-complete

INSTANCE: a tree `G = (V, E)`, a collection `C` of `|E|` not necessarily distinct non-negative
integers, and a positive integer `K`.
QUESTION: is there a one-to-one function `f : E → C` such that, if `f(e)` is taken as the length
of edge `e`, then `G` has radius `K` or less, i.e., there is a vertex `c ∈ V` such that every
`v ∈ V` is joined to `c` by a path in `G` of length `K` or less?

This is WEIGHTED DIAMETER ([GT65], `WeightedDiameterWanted`) with "diameter" replaced by
"radius", restricted to trees: Garey and Johnson record that WEIGHTED DIAMETER is NP-complete in
the strong sense even if `G` is a tree, and that the radius variant has the same complexity. The
instance type, `WeightedDiameter.Graph`, `WeightedDiameter.WellFormed` (a simple edge list on
`Fin n`, `|C| = |E|`, `0 < K`) and `WeightedDiameter.weightedLength` (the length of a walk when
the `k`-th listed edge gets `ℓ[k]`) are reused unchanged, and an assignment is again a
rearrangement `ℓ` of `C`. `WellFormed` adds that the graph is a tree (Mathlib's
`SimpleGraph.IsTree`).

The radius of `G` is `min_c max_v dist(c, v)`; it is at most `K` exactly when some centre `c` is
joined to every vertex by a path of length at most `K` (`WeightedRadiusFeasible`). Numbers use
the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WEIGHTED RADIUS is NP-complete for trees.** Source: Garey and Johnson (1979), [GT65],
comment (Perl and Zaks, 1978). -/
public theorem_wanted weightedRadiusTrees_npComplete :
    weightedRadiusTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedRadiusTreesDec

end MetaMathlibExt.Complexity.NPComplete.WeightedRadiusTrees
