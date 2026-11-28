/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSHUFFLING A SQUARE is NP-complete

Source:
S. Buss and M. Soltys, "Unshuffling a square is NP-hard", Journal of Computer and System
Sciences 80(4) (2014), 766-776, doi:10.1016/j.jcss.2013.11.002, arXiv:1211.7161
(Section 1, definition of shuffle and square; Theorem 3).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShuffleSquareDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShuffleSquare

/-!
# UNSHUFFLING A SQUARE is NP-complete

INSTANCE: a string `w` over an alphabet `Σ`.
QUESTION: is `w` a square, that is, is `w` a shuffle `u ⊙ u` of some string `u` with itself?

As in Buss and Soltys, `w` is a shuffle of `u` and `v` when there are (possibly empty) strings
`xᵢ` and `yᵢ` such that `u = x₁ x₂ ⋯ xₖ`, `v = y₁ y₂ ⋯ yₖ` and `w = x₁ y₁ x₂ y₂ ⋯ xₖ yₖ`, that is,
when `w` interleaves `u` and `v` keeping the order of each. This is the repository's
`Cslib.Language.IsShuffle u v w` (`CSLibExt.Computability.Languages.Shuffle`), which builds `w`
one symbol at a time, taken from the front of `u` or of `v`.

Symbols are natural numbers, so the alphabet is part of the input (the symbols occurring in
`w`). Buss and Soltys prove NP-completeness for general alphabets, and also for every fixed
alphabet with at least 7 symbols; this statement is the general-alphabet problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNSHUFFLING A SQUARE is NP-complete.** Source: Buss and Soltys (2014),
Theorem 3. -/
public theorem_wanted shuffleSquare_npComplete :
    shuffleSquareDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shuffleSquareDec

end MetaMathlibExt.Complexity.NPComplete.ShuffleSquare
