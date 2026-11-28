/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSEST SUBSTRING is NP-complete

Source:
J. K. Lanctot, M. Li, B. Ma, S. Wang, and L. Zhang, "Distinguishing string selection
problems", Information and Computation 185 (2003), 41-55,
doi:10.1016/S0890-5401(03)00057-9;
M. Frances and A. Litman, "On covering problems of codes", Theory of Computing Systems 30
(1997), 113-119, doi:10.1007/BF02679443 (CLOSEST STRING, the special case `L = |sᵢ|`, is
NP-complete over the binary alphabet).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ClosestSubstringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosestSubstring

/-!
# CLOSEST SUBSTRING is NP-complete

INSTANCE: an alphabet `Σ`, strings `s₁, ..., s_k` over `Σ` (of arbitrary lengths), a positive
integer `L ≤ min |sᵢ|`, and a nonnegative integer `d`. QUESTION: is there a string `t` of length
`L` over `Σ` such that every `sᵢ` has a substring (a block of consecutive letters) of length `L`
within Hamming distance `d` of `t`?

Representation. The alphabet is `Σ = {0, ..., a - 1}`, given by its size `a`; strings are lists
of letters. The candidate `t` is a word `Fin L → ℕ` with letters below `a`, the length-`L`
substring of `s` starting at position `j` (with `j + L ≤ |s|`) is the word
`k ↦ s[j + k]`, and the distance is Mathlib's `hammingDist`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLOSEST SUBSTRING is NP-complete.** Source: Lanctot, Li, Ma, Wang, and Zhang (2003);
Frances and Litman (1997). -/
public theorem_wanted closestSubstring_npComplete :
    closestSubstringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L closestSubstringDec

end MetaMathlibExt.Complexity.NPComplete.ClosestSubstring
