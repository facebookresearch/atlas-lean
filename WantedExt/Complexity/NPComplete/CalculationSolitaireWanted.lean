/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED CALCULATION SOLITAIRE is NP-complete

Source:
C. Iwamoto and T. Ide, "Calculation Solitaire is NP-complete", IEICE Transactions on
Information and Systems E106-D (2023), 328-332, doi:10.1587/transinf.2022FCL0002, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CalculationSolitaireDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CalculationSolitaire

/-!
# GENERALIZED CALCULATION SOLITAIRE is NP-complete

Calculation is a solitaire card game (Iwamoto and Ide, Section 1). The generalized
`(s × k)`-card deck has `s` suits of `k` ranks `1, …, k`, where `k` is prime; suits play no
role. The `i`-foundation (`1 ≤ i ≤ s`) starts with a card `i` and is built up by `i`s until a
card `k` is reached, a card of rank `r` being usable as a card of rank `r + k j`: its cards are,
in order, the ranks congruent to `i, 2i, 3i, …, ki` modulo `k`, the last one being `k`. The
player moves (i) the top card of the stock either onto a foundation or to the top of a tableau
pile, or (ii) the top card of a tableau pile onto a foundation.

INSTANCE: a mid-play configuration of the generalized game: `s` foundations, at most `s`
tableau piles, and a stock.
QUESTION: can the player move all cards of the stock and the tableau piles to the foundations?
(Iwamoto and Ide prove this NP-complete, Theorem 1.)

A foundation is determined by its number of cards `h` (`1 ≤ h ≤ k`): the `t`-th card of the
`i`-foundation has rank `card k i t`, the rank in `1, …, k` congruent to `i t` modulo `k`. Its
next card is `card k i (h + 1)` while `h < k`. The tableau piles and the stock are lists of
ranks, top card first. The configuration lists exactly `s` piles, empty ones included, so that
every pile of the game is available (at most `s` of them hold cards). The steps `1, …, s` are
invertible modulo `k` because `s < k` (implicit in the source: otherwise a foundation could not
be built up to `k`). The configuration uses exactly the deck: every rank `1, …, k` occurs `s`
times in total on the foundations, the tableau piles and the stock.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED CALCULATION SOLITAIRE is NP-complete.** Source: Iwamoto and Ide (2023),
Theorem 1. -/
public theorem_wanted calculationSolitaire_npComplete :
    calculationSolitaireDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L calculationSolitaireDec

end MetaMathlibExt.Complexity.NPComplete.CalculationSolitaire
