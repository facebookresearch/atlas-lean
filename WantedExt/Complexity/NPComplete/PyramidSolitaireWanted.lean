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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Prod
public import Mathlib.Logic.Relation

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

/-- An instance: the number of ranks `k`, the pyramid layers (layer `0` first), and the stock
from top to bottom; a card is `(rank, suit)`. -/
abbrev PyramidSolitaireInstance := ℕ × List (List (ℕ × ℕ)) × List (ℕ × ℕ)

/-- The number of layers `l`. -/
def layers (i : PyramidSolitaireInstance) : ℕ := i.2.1.length

/-- The number of stock cards `s`. -/
def stockSize (i : PyramidSolitaireInstance) : ℕ := i.2.2.length

/-- Well-formedness: `k ≥ 1`, layer `j` has `l - j` cards, every card has rank in `1, …, k` and
suit in `0, …, 3`, and the pyramid and stock together are `4k` distinct cards, i.e. the whole
deck. -/
def WellFormed (i : PyramidSolitaireInstance) : Prop :=
  0 < i.1 ∧ (∀ j < layers i, (i.2.1.getD j []).length = layers i - j) ∧
    (∀ x ∈ i.2.1.flatten ++ i.2.2, 1 ≤ x.1 ∧ x.1 ≤ i.1 ∧ x.2 < 4) ∧
    (i.2.1.flatten ++ i.2.2).Nodup ∧ (i.2.1.flatten ++ i.2.2).length = 4 * i.1

/-- The pyramid positions `(j, p)`: layer `j < l`, position `p < l - j`. -/
def positions (i : PyramidSolitaireInstance) : Finset (ℕ × ℕ) :=
  (Finset.range (layers i) ×ˢ Finset.range (layers i)).filter fun x => x.2 < layers i - x.1

/-- The card at pyramid position `x`. -/
def card (i : PyramidSolitaireInstance) (x : ℕ × ℕ) : ℕ × ℕ :=
  (i.2.1.getD x.1 []).getD x.2 (0, 0)

/-- The card at depth `t` of the stock (`0` = top). -/
def stockCard (i : PyramidSolitaireInstance) (t : ℕ) : ℕ × ℕ := i.2.2.getD t (0, 0)

/-- Ranks `a` and `b` match: `a + b = k + 1` for even `k`, `a + b = k` for odd `k`. -/
def Matches (i : PyramidSolitaireInstance) (a b : ℕ) : Prop :=
  a + b = if i.1 % 2 = 0 then i.1 + 1 else i.1

/-- Rank `a` is a King (removed alone): `k` is odd and `a = k`. -/
def IsKing (i : PyramidSolitaireInstance) (a : ℕ) : Prop := i.1 % 2 = 1 ∧ a = i.1

/-- Position `x` is exposed when the positions `R` hold cards: it is in the first layer, or
neither card that covers it is still there. -/
def Exposed (R : Finset (ℕ × ℕ)) (x : ℕ × ℕ) : Prop :=
  x.1 = 0 ∨ ((x.1 - 1, x.2) ∉ R ∧ (x.1 - 1, x.2 + 1) ∉ R)

/-- One move from `(R, t)`: the positions `R` still hold cards and `t` stock cards are gone. -/
inductive Move (i : PyramidSolitaireInstance) : Finset (ℕ × ℕ) × ℕ → Finset (ℕ × ℕ) × ℕ → Prop
  /-- Remove two matching exposed pyramid cards. -/
  | pair {R : Finset (ℕ × ℕ)} {t : ℕ} {x y : ℕ × ℕ} (hxy : x ≠ y) (hx : x ∈ R) (hy : y ∈ R)
      (hex : Exposed R x) (hey : Exposed R y) (hm : Matches i (card i x).1 (card i y).1)
      (ht : t < stockSize i) : Move i (R, t) ((R.erase x).erase y, t)
  /-- Remove an exposed pyramid King. -/
  | king {R : Finset (ℕ × ℕ)} {t : ℕ} {x : ℕ × ℕ} (hx : x ∈ R) (hex : Exposed R x)
      (hk : IsKing i (card i x).1) (ht : t < stockSize i) : Move i (R, t) (R.erase x, t)
  /-- Match the top stock card with an exposed pyramid card. -/
  | stock {R : Finset (ℕ × ℕ)} {t : ℕ} {x : ℕ × ℕ} (hx : x ∈ R) (hex : Exposed R x)
      (hm : Matches i (card i x).1 (stockCard i t).1) (ht : t < stockSize i) :
      Move i (R, t) (R.erase x, t + 1)
  /-- Discard the top stock card. -/
  | discard {R : Finset (ℕ × ℕ)} {t : ℕ} (ht : t < stockSize i) : Move i (R, t) (R, t + 1)

/-- Some sequence of moves removes every pyramid and stock card. -/
def PyramidSolitaireFeasible (i : PyramidSolitaireInstance) : Prop :=
  Relation.ReflTransGen (Move i) (positions i, 0) (∅, stockSize i)

open Classical in
/-- GENERALIZED PYRAMID SOLITAIRE as a decision problem over bitstrings. -/
noncomputable def pyramidSolitaireDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PyramidSolitaireInstance) x with
  | some i => decide (WellFormed i ∧ PyramidSolitaireFeasible i)
  | none => false

/-- **GENERALIZED PYRAMID SOLITAIRE is NP-complete.** Source: Iwamoto and Matsui (2013). -/
public theorem_wanted pyramidSolitaire_npComplete :
    pyramidSolitaireDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pyramidSolitaireDec

end MetaMathlibExt.Complexity.NPComplete.PyramidSolitaire
