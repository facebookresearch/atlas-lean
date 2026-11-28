/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-DIMENSIONAL MATCHING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 3-DIMENSIONAL MATCHING;
R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThreeDimensionalMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching

/-!
# 3-DIMENSIONAL MATCHING is NP-complete

Three parts, each of size `n` (elements `0, …, n - 1`), and a list of triples. The question is
whether some subcollection of triples is a perfect matching: every element of every part
appears in exactly one chosen triple.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **3-DIMENSIONAL MATCHING is NP-complete.** The decision problem 3-DIMENSIONAL MATCHING on
bitstrings is in NP, and every decision problem in NP reduces to it by a polynomial-time many-one
reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), 3-DIMENSIONAL MATCHING; R. M. Karp, "Reducibility
among combinatorial problems" (1972). -/
public theorem_wanted threeDimensionalMatching_npComplete :
    threeDimensionalMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeDimensionalMatchingDec

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching
