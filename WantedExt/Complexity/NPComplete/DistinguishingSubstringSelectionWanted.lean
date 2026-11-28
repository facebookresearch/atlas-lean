/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISTINGUISHING SUBSTRING SELECTION is NP-complete

Source:
J. K. Lanctot, M. Li, B. Ma, S. Wang and L. Zhang, "Distinguishing string selection problems",
Information and Computation 185 (2003), 41-55, doi:10.1016/S0890-5401(03)00057-9;
J. Gramm, J. Guo and R. Niedermeier, "Parameterized intractability of distinguishing substring
selection", Theory of Computing Systems 39 (2006), 545-560, doi:10.1007/s00224-004-1185-z.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DistinguishingSubstringSelectionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DistinguishingSubstringSelection

open ClosestSubstring (substringAt)

/-!
# DISTINGUISHING SUBSTRING SELECTION is NP-complete

INSTANCE: an alphabet `Σ`, "bad" strings `B₁, ..., Bₘ` and "good" strings `G₁, ..., Gₙ` over
`Σ`, each of length at least `L`, and integers `L`, `k_b` and `k_g`.
QUESTION: is there a string `t ∈ Σ^L` such that every bad string has a length-`L` substring
within Hamming distance `k_b` of `t`, and every length-`L` substring of every good string has
Hamming distance at least `k_g` from `t`?

This is the statement of Gramm, Guo and Niedermeier ("given integers `d_g`, `d_b`, and `L`, we
ask for a length-`L` string `s` such that `s` has Hamming distance at least `d_g` to every
length-`L` substring of the good strings and such that every bad string has a length-`L`
substring with Hamming distance at most `d_b` to `s`"), with `k_b = d_b` and `k_g = d_g`. With
no good strings it is CLOSEST SUBSTRING (`ClosestSubstringWanted`), which Lanctot et al. prove
NP-hard; with every string of length `L` it is DISTINGUISHING STRING SELECTION
(`DistinguishingStringSelectionWanted`).

The alphabet is `{0, ..., q - 1}`, given by its size `q`; strings are lists of letters; the
candidate `t` is a word `Fin L → ℕ` with letters below `q`; the length-`L` substring of `s`
starting at position `j` (with `j + L ≤ |s|`) is `ClosestSubstring.substringAt s j L`; and the
distance is Mathlib's `hammingDist`. Lengths and distance bounds use the canonical binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DISTINGUISHING SUBSTRING SELECTION is NP-complete.** Source: Lanctot, Li, Ma, Wang and
Zhang (2003); Gramm, Guo and Niedermeier (2006). -/
public theorem_wanted distinguishingSubstringSelection_npComplete :
    distinguishingSubstringSelectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L distinguishingSubstringSelectionDec

end MetaMathlibExt.Complexity.NPComplete.DistinguishingSubstringSelection
