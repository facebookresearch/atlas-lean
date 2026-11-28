/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KLONDIKE SOLITAIRE is NP-complete

Source:
L. Longpré and P. McKenzie, "The complexity of Solitaire", Theoretical Computer Science 410(50)
(2009), 5252-5260, doi:10.1016/j.tcs.2009.08.027 (Section 2.2, Definition 1, Theorem 2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KlondikeSolitaireDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KlondikeSolitaire

open MetaMathlibExt.Complexity.NPComplete.FreeCell (Card deck Matches)

/-!
# KLONDIKE SOLITAIRE is NP-complete

Longpré and McKenzie (2009) study thoughtful Klondike, in which the player sees the complete
game configuration, generalized to `n` cards `1, …, n` in each of four suits, two black and two
red, and any number of build stacks of any size. Their rules (Section 2.2, quoting Yan,
Diaconis, Rusmevichientong and Van Roy): the goal is to move all cards into the suit stacks,
aces first, then two's, and so on, each suit stack an increasing arrangement of cards of one
suit. On each turn the player can:
1. move the face-up cards of a build stack (a card block; all of them together, order kept) to
   the top of another build stack that accepts the block; the card beneath the block, now the
   top card of its stack, is turned face up;
2. move the top face-up card of a build stack to the top of a suit stack that accepts it;
3. move the top card of a suit stack to the top of a build stack that accepts it;
4. if the pile is not empty, deal its top three cards to the talon, which keeps its cards in
   first-in-last-out order; if the pile is empty, redeal all the cards of the talon back to the
   pile in one move, preserving their order (unlimited redeals);
5. move the top card of the talon to the top of a build stack or a suit stack that accepts it.

Rule 1 moves the whole face-up part of the source stack: the paper says "Note that all faceup
cards on the source stack must be moved together", and its NP upper bound (proof of Theorem 2)
counts every move from build stack to build stack as a move that turns a face-down card face up
or empties the stack, which holds only under this rule. Common Klondike software also lets a
player move only the top part of the face-up cards; this statement follows the paper's rules,
the game Theorem 2 is about.

Acceptance: 6. a build stack accepts a block if its top card is adjacent to (one rank higher
than) and braided with (of the other color than) the bottom card of the block; an empty build
stack accepts only a block whose bottom card is a King (rank `n`). 7. a suit stack accepts only
a card of its suit: an Ace if it is empty, otherwise the card one rank above its top card.

Definition 1 (`Solit(2, 2)`, called Solitaire): given an initial configuration with four suits
of `n` cards each, can all the cards be placed on the suit stacks by the rules? Theorem 2:
Solitaire is NP-complete.

The instance is `(n, build stacks, pile)`; each list of cards runs from the bottom card to the
top card. Cards are `FreeCell.Card`s `(suit, value)`; suits `0, 1` (`♦, ♥`) are red and `2, 3`
(`♣, ♠`) black (`FreeCell.IsRed`), so "top card `y` adjacent to and braided with `x`" is
`FreeCell.Matches x`. As in a Klondike deal, the top card of each build stack starts face up and
the others face down; the talon and the four suit stacks start empty. `WellFormed` requires
`n ≥ 1`, nonempty build stacks, and every card of the deck `FreeCell.deck n` exactly once.

A configuration lists each build stack as its face-down and face-up cards, the heights of the
four suit stacks (suit stack `s` holds the cards `1, …, h` of suit `s`), the pile and the talon.
When fewer than three cards remain in the pile, a deal moves all of them (the source says "its
top three cards"); the NP-hardness proof of Theorem 2 starts with an empty pile and talon, so
this convention does not affect it. The game is won when every suit stack holds `n` cards.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **KLONDIKE SOLITAIRE is NP-complete.** Source: Longpré and McKenzie (2009), Theorem 2. -/
public theorem_wanted klondikeSolitaire_npComplete :
    klondikeSolitaireDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L klondikeSolitaireDec

end MetaMathlibExt.Complexity.NPComplete.KlondikeSolitaire
