/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SORTING BY PREFIX REVERSALS (PANCAKE FLIPPING) is NP-complete

Source:
L. Bulteau, G. Fertin and I. Rusu, "Pancake flipping is hard", Journal of Computer and System
Sciences 81(8) (2015), 1556-1574, doi:10.1016/j.jcss.2015.02.003, Theorem 2 (Sorting By
Prefix Reversals is NP-hard, by a reduction from 3-SAT); preprint arXiv:1111.0434.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PancakeFlippingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PancakeFlipping

/-!
# SORTING BY PREFIX REVERSALS (PANCAKE FLIPPING) is NP-complete

INSTANCE: a permutation `π` of `{1, …, n}` and an integer `K`.
QUESTION: can `π` be sorted (turned into the identity `1, 2, …, n`) by at most `K` prefix
reversals, where the prefix reversal (flip) of length `r`, `1 ≤ r ≤ n`, reverses the first `r`
elements of the sequence?

The permutation is the list `x₁, …, xₙ` of its values. The flip of length `r` transforms
`x₁, …, x_r, x_{r+1}, …, xₙ` into `x_r, …, x₁, x_{r+1}, …, xₙ`; a sequence of flips is
applied from the first to the last.

Membership in NP: every permutation can be sorted with at most `2n` flips (bring the largest
unsorted element to the front, then flip it into place), so a shortest sorting sequence is a
certificate of polynomial size whenever one of length at most `K` exists.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SORTING BY PREFIX REVERSALS (PANCAKE FLIPPING) is NP-complete.** Source: Bulteau, Fertin and
Rusu (2015), Theorem 2. -/
public theorem_wanted pancakeFlipping_npComplete :
    pancakeFlippingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pancakeFlippingDec

end MetaMathlibExt.Complexity.NPComplete.PancakeFlipping
