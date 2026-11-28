/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FARTHEST STRING is NP-complete

Source:
J. K. Lanctot, M. Li, B. Ma, S. Wang, and L. Zhang, "Distinguishing string
selection problems", Information and Computation 185 (2003), 41-55,
doi:10.1016/S0890-5401(03)00057-9 (preliminary version: Proc. 10th ACM-SIAM SODA
(1999)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FarthestStringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FarthestString

open DistinguishingStringSelection (DistinguishingStringSelectionInstance IsWord asWord
  DistinguishingStringSelectionFeasible)

/-!
# FARTHEST STRING is NP-complete

INSTANCE: an alphabet `Σ`, strings `s₁, ..., s_k ∈ Σ^L`, and a nonnegative integer `d`.
QUESTION: is there a string `t ∈ Σ^L` with `d_H(t, sᵢ) ≥ d` for every `i`?

Lanctot et al. prove the Farthest String Problem NP-hard; it is in NP because `t` is a short
certificate. It is DISTINGUISHING STRING SELECTION (`DistinguishingStringSelectionWanted`) with
no bad strings: the given strings are the good strings and `d` is the far threshold `k_g`. The
statement reuses that module's instance, well-formedness and question on the instance
`toDistinguishing i`, so the alphabet is `{0, ..., q - 1}`, strings are lists of symbols, and
`d_H` is Mathlib's `hammingDist` on strings of length `L` read as functions `Fin L → ℕ`
(`farthestStringFeasible_iff` unfolds the question). Lengths and the bound `d` use the canonical
binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FARTHEST STRING is NP-complete.** Source: Lanctot, Li, Ma, Wang, and Zhang (2003). -/
public theorem_wanted farthestString_npComplete :
    farthestStringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L farthestStringDec

end MetaMathlibExt.Complexity.NPComplete.FarthestString
