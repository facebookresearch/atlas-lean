/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED FREECELL is NP-complete

Source:
M. Helmert, "Complexity results for standard benchmark domains in planning", Artificial
Intelligence 143(2) (2003), 219-262, doi:10.1016/S0004-3702(02)00364-8, Section 4.3,
Definitions 44 (FREECELL task) and 45 (FREECELL domain) and Theorem 46 (plan existence for
FREECELL is NP-complete, even for an arbitrary fixed number of free cells).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FreeCell

/-!
# GENERALIZED FREECELL is NP-complete

INSTANCE (a FREECELL task `(n, w, c, T)`, Helmert, Definition 44): a suit length `n`, a tableau
width `w`, a free cell count `c`, and an initial tableau `T`: at most `w` non-empty sequences
(tableau piles) of cards of the `n`-deck `{♦, ♥, ♣, ♠} × {1, …, n}` in which every card of the
deck appears exactly once.
QUESTION: can all cards be moved to the foundations by legal moves (plan existence for the
FREECELL domain, Definition 45)?

Moves (Definition 45). A state is a pair `(T, F)` of a tableau and the set `F` of free cell
cards, `|F| ≤ c`; cards in neither are on the foundations. The initial state is `(T, ∅)`, the
goal is `(∅, ∅)`. The last card of a pile is its top card. A move is a pickup followed by a drop
of the same card. Pickups: from a free cell; from the tableau, when the card is the only card of
its pile (the pile disappears); from a tableau pile, when the card is the top card of a pile with
a non-empty buried part. Drops: in a free cell, when fewer than `c` free cells are occupied; on
the tableau, as a new one-card pile, when there are fewer than `w` piles; on a tableau pile whose
top card it matches (different colour, value one less); at the foundations, when no tableau or
free cell card of the same suit has a lower value.

Cards are pairs `(suit, value)` with suits `0, 1, 2, 3` standing for `♦, ♥, ♣, ♠`, so a card is
red iff its suit is below `2`. Piles are lists listed from the bottom card to the top card;
the tableau and the free cells are lists whose order is immaterial (every move may act at any
position).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A card `(suit, value)`: suits `0, 1, 2, 3` are `♦, ♥, ♣, ♠`. -/
abbrev Card := ℕ × ℕ

/-- An instance (FREECELL task): suit length `n`, tableau width `w`, free cell count `c`, and
the initial tableau (piles listed from bottom to top card). -/
abbrev FreeCellInstance := ℕ × ℕ × ℕ × List (List Card)

/-- A state: the current tableau (piles, bottom to top) and the free cell cards. -/
abbrev State := List (List Card) × List Card

/-- The `n`-deck `{♦, ♥, ♣, ♠} × {1, …, n}`. -/
def deck (n : ℕ) : List Card :=
  (List.range 4).flatMap fun s => (List.range' 1 n).map fun v => (s, v)

/-- A card is red iff its suit is `♦` (`0`) or `♥` (`1`). -/
def IsRed (x : Card) : Prop := x.1 < 2

/-- Card `x` matches pile `p`: `p` has a top card `y` of the other colour, and the value of `x`
is one less than the value of `y`. -/
def Matches (x : Card) (p : List Card) : Prop :=
  ∃ b y, p = b ++ [y] ∧ (IsRed x ↔ ¬ IsRed y) ∧ x.2 + 1 = y.2

/-- Pickup activities: picking up card `x` in state `s` leaves state `t`. -/
def Pickup (s : State) (x : Card) (t : State) : Prop :=
  (∃ A B, s.2 = A ++ x :: B ∧ t = (s.1, A ++ B)) ∨
    (∃ P Q, s.1 = P ++ [x] :: Q ∧ t = (P ++ Q, s.2)) ∨
    (∃ P Q b, b ≠ [] ∧ s.1 = P ++ (b ++ [x]) :: Q ∧ t = (P ++ b :: Q, s.2))

/-- Drop activities for tableau width `w` and free cell count `c`: dropping card `x` in state
`t` gives state `s`. -/
def Drop (w c : ℕ) (t : State) (x : Card) (s : State) : Prop :=
  (∃ A B, t.2 = A ++ B ∧ t.2.length < c ∧ s = (t.1, A ++ x :: B)) ∨
    (∃ P Q, t.1 = P ++ Q ∧ t.1.length < w ∧ s = (P ++ [x] :: Q, t.2)) ∨
    (∃ P Q q, t.1 = P ++ q :: Q ∧ Matches x q ∧ s = (P ++ (q ++ [x]) :: Q, t.2)) ∨
    ((∀ y ∈ t.1.flatten ++ t.2, y.1 = x.1 → ¬ y.2 < x.2) ∧ s = t)

/-- A legal move of the task: a pickup followed by a drop of the same card. -/
def Move (i : FreeCellInstance) (s s' : State) : Prop :=
  ∃ x t, Pickup s x t ∧ Drop i.2.1 i.2.2.1 t x s'

/-- Well-formedness of an instance: the initial tableau has at most `w` piles, every pile is
non-empty, and every card of the `n`-deck appears exactly once. -/
def WellFormed (i : FreeCellInstance) : Prop :=
  i.2.2.2.length ≤ i.2.1 ∧ (∀ p ∈ i.2.2.2, p ≠ []) ∧ i.2.2.2.flatten.Perm (deck i.1)

/-- Plan existence: legal moves lead from the initial state `(T, ∅)` to the goal `(∅, ∅)`. -/
def FreeCellFeasible (i : FreeCellInstance) : Prop :=
  Relation.ReflTransGen (Move i) (i.2.2.2, []) ([], [])

open Classical in
/-- GENERALIZED FREECELL as a decision problem over bitstrings. -/
noncomputable def freeCellDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FreeCellInstance) x with
  | some i => decide (WellFormed i ∧ FreeCellFeasible i)
  | none => false

/-- **GENERALIZED FREECELL is NP-complete.** Source: Helmert (2003), Theorem 46. -/
public theorem_wanted freeCell_npComplete :
    freeCellDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L freeCellDec

end MetaMathlibExt.Complexity.NPComplete.FreeCell
