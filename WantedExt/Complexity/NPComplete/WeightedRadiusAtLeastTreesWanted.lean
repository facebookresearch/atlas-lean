/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER, radius `K` or greater for trees, is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER, p. 205,
comment: the variant asking for an assignment yielding diameter `K` or greater is NP-complete
for trees in the radius case (reference: Y. Perl and S. Zaks (1978), private communication);
see also Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical
Computer Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeightedRadiusAtLeastTreesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedRadiusAtLeastTrees

/-!
# WEIGHTED DIAMETER, radius `K` or greater for trees, is NP-complete

INSTANCE: a tree `G = (V, E)`, a collection `C` of `|E|` not necessarily distinct non-negative
integers, and a positive integer `K`. QUESTION: is there a one-to-one function `f : E → C` such
that, if `f(e)` is taken as the length of edge `e`, then `G` has radius `K` or greater?

This is the variant of WEIGHTED DIAMETER that Garey and Johnson's comment records as
NP-complete for trees: "radius" replaces "diameter" (radius `K` or less: some vertex is joined
to every vertex by a path of length `K` or less), and the question asks for radius `K` or
greater. That is read as the negation of the radius condition for `K - 1`: for every vertex `v`
some vertex `u` is joined to `v` by no path of length less than `K`, i.e., every path from `v`
to `u` has length at least `K`. The graph is a tree (Mathlib's `SimpleGraph.IsTree`: connected
and acyclic, so `V` is nonempty) by `WellFormed`. A path is a Mathlib `SimpleGraph.Walk` that
`IsPath`, and its length is the sum of the lengths of its edges.

`C` is a list of length `|E|`, and the one-to-one function `f : E → C` is a rearrangement `w` of
that list (`List.Perm`): the `j`-th edge of the edge list gets length `w[j]`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. Numbers use the canonical binary
encoding.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WEIGHTED DIAMETER, radius `K` or greater for trees, is NP-complete.** Source: Garey and
Johnson (1979), [GT65], comment (Perl and Zaks, 1978). -/
public theorem_wanted weightedRadiusAtLeastTrees_npComplete :
    weightedRadiusAtLeastTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedRadiusAtLeastTreesDec

end MetaMathlibExt.Complexity.NPComplete.WeightedRadiusAtLeastTrees
