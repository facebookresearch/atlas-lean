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
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import WantedExt.Complexity.NPComplete.FreeCellWanted

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

/-- An instance: the number `n` of cards per suit, the build stacks and the pile, each listed
from the bottom card to the top card. -/
abbrev KlondikeSolitaireInstance := ℕ × List (List Card) × List Card

/-- A game configuration: the build stacks as (face-down cards, face-up cards), the heights of
the suit stacks `0, …, 3`, the pile and the talon; card lists run from bottom to top. -/
structure Config where
  /-- The build stacks: face-down cards and face-up cards, each from bottom to top. -/
  builds : List (List Card × List Card)
  /-- The height of each suit stack: suit stack `s` holds the cards `1, …, suits[s]` of suit
  `s`. -/
  suits : List ℕ
  /-- The pile, from bottom to top. -/
  pile : List Card
  /-- The talon, from bottom to top. -/
  talon : List Card

/-- After face-up cards leave a build stack: if none is left, the top face-down card (if any)
is turned face up. -/
def turnUp : List Card × List Card → List Card × List Card
  | (d, []) => (d.dropLast, d.getLast?.toList)
  | p => p

/-- Build stack `x` (face-down, face-up) accepts a block, or a card, whose bottom card is `c`:
`x` is empty and `c` is a King, or the top card of `x` is adjacent to and braided with `c`. -/
def Accepts (n : ℕ) (x : List Card × List Card) (c : Card) : Prop :=
  (x = ([], []) ∧ c.2 = n) ∨ Matches c x.2

/-- One move of the game with `n` cards per suit (rules 1-7). -/
def Step (n : ℕ) (s t : Config) : Prop :=
  -- 1. all face-up cards of build stack `j` onto build stack `k`, which accepts the block
  (∃ j k d u x, j ≠ k ∧ s.builds[j]? = some (d, u) ∧ s.builds[k]? = some x ∧
    (∃ c, u.head? = some c ∧ Accepts n x c) ∧
    t = { s with builds := (s.builds.set j (turnUp (d, []))).set k (x.1, x.2 ++ u) }) ∨
  -- 2. the top face-up card `c` of build stack `j` onto its suit stack
  (∃ j d u c h, s.builds[j]? = some (d, u ++ [c]) ∧ s.suits[c.1]? = some h ∧ c.2 = h + 1 ∧
    t = { s with builds := s.builds.set j (turnUp (d, u)), suits := s.suits.set c.1 c.2 }) ∨
  -- 3. the top card of suit stack `q` onto build stack `j`, which accepts it
  (∃ j x q h, s.builds[j]? = some x ∧ s.suits[q]? = some (h + 1) ∧ Accepts n x (q, h + 1) ∧
    t = { s with builds := s.builds.set j (x.1, x.2 ++ [(q, h + 1)]),
                 suits := s.suits.set q h }) ∨
  -- 4. deal the top three cards of a nonempty pile (all, if fewer remain) to the talon, one by
  -- one; or, with the pile empty, redeal the talon to the pile, preserving the order
  (s.pile ≠ [] ∧
    t = { s with pile := s.pile.take (s.pile.length - 3),
                 talon := s.talon ++ (s.pile.drop (s.pile.length - 3)).reverse }) ∨
  (s.pile = [] ∧ t = { s with pile := s.talon.reverse, talon := [] }) ∨
  -- 5. the top card `c` of the talon onto a build stack that accepts it, or onto its suit stack
  (∃ r c, s.talon = r ++ [c] ∧
    ((∃ j x, s.builds[j]? = some x ∧ Accepts n x c ∧
        t = { s with builds := s.builds.set j (x.1, x.2 ++ [c]), talon := r }) ∨
      (∃ h, s.suits[c.1]? = some h ∧ c.2 = h + 1 ∧
        t = { s with suits := s.suits.set c.1 c.2, talon := r })))

/-- Well-formedness: `n ≥ 1`, every build stack is nonempty, and the build stacks and the pile
hold every card of the `n`-card four-suit deck exactly once. -/
def WellFormed (i : KlondikeSolitaireInstance) : Prop :=
  1 ≤ i.1 ∧ (∀ b ∈ i.2.1, b ≠ []) ∧ (i.2.1.flatten ++ i.2.2).Perm (deck i.1)

/-- The initial configuration: the top card of each build stack face up, the rest face down,
empty suit stacks and an empty talon. -/
def init (i : KlondikeSolitaireInstance) : Config :=
  { builds := i.2.1.map fun b => (b.dropLast, b.getLast?.toList)
    suits := [0, 0, 0, 0]
    pile := i.2.2
    talon := [] }

/-- The game can be won: moves lead from the initial configuration to one where every suit
stack holds `n` cards. -/
def KlondikeSolitaireFeasible (i : KlondikeSolitaireInstance) : Prop :=
  ∃ t, Relation.ReflTransGen (Step i.1) (init i) t ∧ t.suits = [i.1, i.1, i.1, i.1]

open Classical in
/-- KLONDIKE SOLITAIRE as a decision problem over bitstrings. -/
noncomputable def klondikeSolitaireDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KlondikeSolitaireInstance) x with
  | some i => decide (WellFormed i ∧ KlondikeSolitaireFeasible i)
  | none => false

/-- **KLONDIKE SOLITAIRE is NP-complete.** Source: Longpré and McKenzie (2009), Theorem 2. -/
public theorem_wanted klondikeSolitaire_npComplete :
    klondikeSolitaireDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L klondikeSolitaireDec

end MetaMathlibExt.Complexity.NPComplete.KlondikeSolitaire
