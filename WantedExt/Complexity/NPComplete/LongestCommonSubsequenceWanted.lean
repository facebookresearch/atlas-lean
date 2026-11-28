/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST COMMON SUBSEQUENCE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LONGEST COMMON
SUBSEQUENCE; D. Maier, "The complexity of some problems on subsequences and supersequences"
(1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LongestCommonSubsequenceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestCommonSubsequence

/-!
# LONGEST COMMON SUBSEQUENCE is NP-complete

A list of binary strings (lists of Booleans) and a bound `K`. The question is whether the
strings have a common subsequence of length at least `K`. Two-string LCS is polynomial; the
number of strings is part of the input.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LONGEST COMMON SUBSEQUENCE is NP-complete.** The LONGEST COMMON SUBSEQUENCE decision
problem, over binary strings, belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), LONGEST COMMON SUBSEQUENCE; D. Maier, "The
complexity of some problems on subsequences and supersequences" (1978). -/
public theorem_wanted longestCommonSubsequence_npComplete :
    longestCommonSubsequenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestCommonSubsequenceDec

end MetaMathlibExt.Complexity.NPComplete.LongestCommonSubsequence
