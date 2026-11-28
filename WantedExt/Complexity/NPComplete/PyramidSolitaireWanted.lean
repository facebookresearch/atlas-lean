/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED PYRAMID SOLITAIRE is NP-complete

Source:
C. Iwamoto and Y. Matsui, "Generalized Pyramid is NP-complete", IEICE Transactions on
Information and Systems E96-D(11) (2013), 2462-2465, doi:10.1587/transinf.E96.D.2462.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PyramidSolitaireDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PyramidSolitaire

/-!
# GENERALIZED PYRAMID SOLITAIRE is NP-complete

Pyramid is a solitaire game whose object is to remove all cards from a pyramidal layout and a
stock of cards. The rules, as stated by Iwamoto and Matsui (2013, Section 1):
* The pyramidal layout has `l` layers: the `l` cards of the first layer cover the `l - 1` cards
  of the second layer, which cover the `l - 2` cards of the third layer, and so on. The other
  cards are piled up as the stock.
* A card is exposed if no cards cover it. Initially the cards of the first layer and the top
  card of the stock are exposed.
* Two exposed cards can be matched and removed if their values match (total 13 in the standard
  game). Exposed cards of value 13 (Kings) can be removed immediately.
* The top card of the stock can be matched only with an exposed card in the pyramid. If no
  match is made, the top card of the stock can be discarded.
* Once the stock is exhausted or no more pairs can be made, the game ends. The aim is to remove
  all of the cards of the pyramid and the stock.

The generalized `4k`-card deck has `k` ranks in each of the four suits. When `k` is even, a
card of rank `r ≤ k / 2` matches a card of rank `k - r + 1`; when `k` is odd, a card of rank
`r ≤ k / 2` matches a card of rank `k - r`, and the cards of rank `k` play the role of Kings.
INSTANCE: an initial layout of the `4k` cards: an `l`-layer pyramid and a stock of
`s = 4k - l(l + 1)/2` cards.
QUESTION: can the player remove all `4k` cards?

A card is `(rank, suit)` with rank in `1, …, k` and suit in `0, …, 3`. The pyramid is a list of
layers, layer `0` being the first (uncovered) layer; layer `j` has `l - j` cards, and the card
in position `p` of layer `j + 1` is covered by the cards in positions `p` and `p + 1` of layer
`j`. The stock is listed from top to bottom. `WellFormed` asks for at least one rank, these
layer lengths, and that the pyramid and stock together are the `4k` distinct cards of the deck.

A position of the game is the set of pyramid positions still holding a card and the number `t`
of stock cards already removed (matched or discarded). The moves are the four removals above.
Following the source's rule that the game ends once the stock is exhausted, every move needs a
nonempty stock (`t < s`). (For even `k`, the case of the source's reduction, this changes
nothing: the top card of the pyramid is covered, directly or not, by every other pyramid card,
so it is removed last and can only be matched with a stock card.)

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED PYRAMID SOLITAIRE is NP-complete.** Source: Iwamoto and Matsui (2013). -/
public theorem_wanted pyramidSolitaire_npComplete :
    pyramidSolitaireDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pyramidSolitaireDec

end MetaMathlibExt.Complexity.NPComplete.PyramidSolitaire
