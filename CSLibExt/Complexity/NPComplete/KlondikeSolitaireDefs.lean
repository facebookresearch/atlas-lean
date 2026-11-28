/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KLONDIKE SOLITAIRE: definitions

Source:
L. Longpré and P. McKenzie, "The complexity of Solitaire", Theoretical Computer Science 410(50)
(2009), 5252-5260, doi:10.1016/j.tcs.2009.08.027 (Section 2.2, Definition 1, Theorem 2).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.FreeCellDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KlondikeSolitaire

open MetaMathlibExt.Complexity.NPComplete.FreeCell (Card deck Matches)

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

end MetaMathlibExt.Complexity.NPComplete.KlondikeSolitaire
