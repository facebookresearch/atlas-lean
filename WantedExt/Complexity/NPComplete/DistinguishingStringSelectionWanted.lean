/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISTINGUISHING STRING SELECTION is NP-complete

Source:
J. K. Lanctot, M. Li, B. Ma, S. Wang, and L. Zhang, "Distinguishing string
selection problems", Information and Computation 185 (2003), 41-55,
doi:10.1016/S0890-5401(03)00057-9 (preliminary version: Proc. 10th ACM-SIAM SODA
(1999)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DistinguishingStringSelectionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DistinguishingStringSelection

/-!
# DISTINGUISHING STRING SELECTION is NP-complete

INSTANCE: an alphabet `Σ`; "bad" strings `B₁, ..., Bₘ` and "good" strings `G₁, ..., Gₙ`, all in
`Σ^L`; nonnegative integers `k_b` and `k_g`. QUESTION: is there a string `t ∈ Σ^L` with
`d_H(t, Bᵢ) ≤ k_b` for all `i` and `d_H(t, Gⱼ) ≥ k_g` for all `j`?

The direction of the two bounds is the source's: Lanctot et al. write the bad strings as `B_c`
and the good strings as `G_f`, with thresholds `k_c` and `k_f` ("c" for close, "f" for far). In
their drug-target application the selected string must be close to every bad (pathogen) string
and far from every good (host) string; Wang and Zhu (FAW 2009, doi:10.1007/978-3-642-02270-8_27)
state the problem the same way, with bad genes close and good genes far.

The alphabet is `{0, ..., q - 1}` and strings are lists of symbols. `d_H` is Mathlib's
`hammingDist`, applied to strings of length `L` read as functions `Fin L → ℕ`. With no good strings
this is CLOSEST STRING, which Lanctot et al. prove NP-hard; the problem is in NP because `t` is a
short certificate. Lengths and distance bounds use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DISTINGUISHING STRING SELECTION is NP-complete.** Source: Lanctot, Li, Ma, Wang, and
Zhang (2003). -/
public theorem_wanted distinguishingStringSelection_npComplete :
    distinguishingStringSelectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L distinguishingStringSelectionDec

end MetaMathlibExt.Complexity.NPComplete.DistinguishingStringSelection
