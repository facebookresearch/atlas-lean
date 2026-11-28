/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED COMPONENT SUM, upper-bound variant with K = 3 and 0/1 entries, is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP18] EXPECTED COMPONENT SUM,
pp. 224-225 (comment: "The variant in which we ask for a partition with K non-empty sets that
yields a sum of B or less is NP-complete even if K is fixed at 3 and all entries are 0's and
1's.").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ExpectedComponentSumUpperBoundThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSumUpperBoundThree

open MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSum

/-!
# EXPECTED COMPONENT SUM, upper-bound variant with K = 3 and 0/1 entries, is NP-complete

The variant of EXPECTED COMPONENT SUM ([SP18], `ExpectedComponentSumWanted`) that asks for a
partition into `K` non-empty sets with component sum at most `B`, with `K = 3` and all
entries in `{0, 1}`. INSTANCE: a collection `C` of `m`-dimensional vectors with entries in
`{0, 1}`, `K = 3`, and a positive integer `B`. QUESTION: is there a partition of `C` into
three non-empty disjoint sets `C₁, C₂, C₃` such that
`∑_{i=1}^{3} max_{1 ≤ j ≤ m} (∑_{v ∈ C_i} v_j) ≤ B`?

The instance and the component sum are those of `ExpectedComponentSumWanted`, and the
restriction to 0/1 entries is `ExpectedComponentSumZeroOne.WellFormed`; `K = 3` is a
well-formedness condition. A partition into non-empty sets `C_k = f⁻¹(k)` is a surjective
`f : Fin |C| → Fin K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EXPECTED COMPONENT SUM, upper-bound variant with `K = 3` and 0/1 entries, is
NP-complete.** Source: Garey and Johnson (1979), [SP18], comment. -/
public theorem_wanted expectedComponentSumUpperBoundThree_npComplete :
    expectedComponentSumUpperBoundThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L expectedComponentSumUpperBoundThreeDec

end MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSumUpperBoundThree
