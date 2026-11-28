/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER
(p. 205; credited there to Perl and Zaks, 1978, transformation from 3-PARTITION);
Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer
Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeightedDiameterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedDiameter

/-!
# WEIGHTED DIAMETER is NP-complete

INSTANCE: a graph `G = (V, E)`, a collection `C` of `|E|` not necessarily distinct non-negative
integers, and a positive integer `K`.
QUESTION: is there a one-to-one function `f : E → C` such that, if `f(e)` is taken as the length
of edge `e`, then `G` has diameter `K` or less, i.e., every pair of points `u, v ∈ V` is joined by
a path in `G` of length `K` or less?

The collection `C` is a list of `|E|` naturals, repetitions allowed. Since `C` has exactly `|E|`
members, a one-to-one `f : E → C` is a bijection between the edges and the members of `C`; it is
given as a rearrangement `ℓ` of `C` (`ℓ.Perm C`), the `k`-th listed edge receiving the length
`ℓ[k]`. A path is a Mathlib `SimpleGraph.Walk` that `IsPath`; its length is the sum of the
lengths of the edges it traverses (`weightedLength`). Numbers use the binary encoding; Garey and
Johnson record that the problem is NP-complete in the strong sense, even if `G` is a tree.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WEIGHTED DIAMETER is NP-complete.** Source: Garey and Johnson (1979), [GT65]; Perl and
Zaks (1982). -/
public theorem_wanted weightedDiameter_npComplete :
    weightedDiameterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedDiameterDec

end MetaMathlibExt.Complexity.NPComplete.WeightedDiameter
