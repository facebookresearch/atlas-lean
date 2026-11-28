/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSEQUENCE is NP-complete

Source:
K.-J. Räihä and E. Ukkonen, "The shortest common supersequence problem over binary alphabet is
NP-complete", Theoretical Computer Science 16 (1981), 187-198. (D. Maier, "The complexity of
some problems on subsequences and supersequences", JACM 25 (1978), 322-336, proves SCS only for
a five-symbol alphabet; the binary case is Räihä-Ukkonen.)
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShortestCommonSupersequenceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequence

/-!
# SHORTEST COMMON SUPERSEQUENCE is NP-complete

A list of binary strings and a bound `K`. The question is whether the strings have a common
supersequence of length at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHORTEST COMMON SUPERSEQUENCE is NP-complete.** The SHORTEST COMMON SUPERSEQUENCE decision
problem over binary strings belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: K.-J. Räihä and E. Ukkonen, "The
shortest common supersequence problem over binary alphabet is NP-complete", Theoretical
Computer Science 16 (1981), 187-198. (D. Maier, "The complexity of some problems on
subsequences and supersequences", JACM 25 (1978), 322-336, proves SCS only for a five-
symbol alphabet; the binary case is Räihä-Ukkonen.) -/
public theorem_wanted shortestCommonSupersequence_npComplete :
    shortestCommonSupersequenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestCommonSupersequenceDec

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequence
