/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED RADIUS with 0/1 lengths and K = 1 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER (p. 205),
comment "If C consists entirely of 0's and 1's, then both the diameter and radius versions are
solvable in polynomial time for trees, but are NP-complete for general graphs, even if K is fixed
at 2 (diameter) or 1 (radius)" (credited there to Perl and Zaks, 1978);
Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer
Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeightedRadiusZeroOneDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedRadiusZeroOne

open MetaMathlibExt.Complexity.NPComplete.WeightedDiameter (WeightedDiameterInstance)

/-!
# WEIGHTED RADIUS with 0/1 lengths and K = 1 is NP-complete

INSTANCE: a graph `G = (V, E)` and a collection `C` of `|E|` integers, each `0` or `1`.
QUESTION: is there a one-to-one function `f : E → C` such that, if `f(e)` is taken as the length
of edge `e`, then `G` has radius `1` or less, i.e., there is a vertex `c ∈ V` such that every
`v ∈ V` is joined to `c` by a path in `G` of length `1` or less?

This is the radius version of WEIGHTED DIAMETER ([GT65], `WeightedDiameterWanted`) on general
graphs, restricted to collections `C` consisting entirely of `0`s and `1`s and to the bound
`K = 1`. The instance type and `WeightedDiameter.WellFormed` (a simple edge list on `Fin n`,
`|C| = |E|`, `0 < K`) are the parent's, and the question is
`WeightedRadiusTrees.WeightedRadiusFeasible` (some rearrangement `ℓ` of `C` and some centre `c`
joined to every vertex by a path of length at most `K`), all unchanged; `WellFormed` adds that
every member of `C` is `0` or `1` and that `K = 1`. Garey and Johnson record that this restriction
is solvable in polynomial time for trees. The empty graph has no centre, so it is a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WEIGHTED RADIUS with 0/1 lengths is NP-complete for `K = 1`.** Source: Garey and Johnson
(1979), [GT65], comment (Perl and Zaks, 1978). -/
public theorem_wanted weightedRadiusZeroOne_npComplete :
    weightedRadiusZeroOneDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedRadiusZeroOneDec

end MetaMathlibExt.Complexity.NPComplete.WeightedRadiusZeroOne
