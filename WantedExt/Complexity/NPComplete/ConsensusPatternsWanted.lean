/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSENSUS PATTERNS is NP-complete

Source:
M. Li, B. Ma and L. Wang, "Finding similar regions in many sequences", Journal of Computer and
System Sciences 65 (2002), 73-96, doi:10.1006/jcss.2002.1823 (Theorem 1: Consensus Patterns is
NP-hard over an alphabet of size four).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConsensusPatternsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsensusPatterns

open ClosestSubstring (ClosestSubstringInstance substringAt)

/-!
# CONSENSUS PATTERNS is NP-complete

INSTANCE: an alphabet `Σ`, a set `S = {s₁, ..., sₙ}` of strings over `Σ`, each of the same
length `m`, a positive integer `L ≤ m`, and a nonnegative integer `D`.
QUESTION: is there a median string `s` of length `L` and a substring `tᵢ` of length `L` of each
`sᵢ` with `∑ᵢ d_H(s, tᵢ) ≤ D`?

This is the decision version of Li, Ma and Wang's Consensus Patterns problem (minimize the
H-cost `∑ᵢ d_H(s, tᵢ)`), the sum counterpart of CLOSEST SUBSTRING (`ClosestSubstringWanted`).
The instance type and the substrings are CLOSEST SUBSTRING's, reused: the alphabet is
`{0, ..., a - 1}`, given by its size `a`; strings are lists of letters; the length-`L` substring
of `s` starting at position `j` (with `j + L ≤ |s|`) is `ClosestSubstring.substringAt s j L`;
the median `s` is a word `Fin L → ℕ` with letters below `a`; and `d_H` is Mathlib's
`hammingDist`. `WellFormed` is CLOSEST SUBSTRING's (at least one string, letters in the
alphabet, `0 < L ≤ |sᵢ|`) plus the source's conditions that the strings are distinct (`S` is a
set) and all have the same length. The start positions of the chosen substrings are a list `js`
with one entry per string, and the H-cost is the sum over the pairs `(sᵢ, jᵢ)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONSENSUS PATTERNS is NP-complete.** Source: Li, Ma and Wang (2002), Theorem 1. -/
public theorem_wanted consensusPatterns_npComplete :
    consensusPatternsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L consensusPatternsDec

end MetaMathlibExt.Complexity.NPComplete.ConsensusPatterns
