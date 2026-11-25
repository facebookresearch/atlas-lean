/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PEG SOLITAIRE (GENERALIZED HI-Q) is NP-complete

Source:
R. Uehara and S. Iwata, "Generalized Hi-Q is NP-complete", Transactions of the IEICE E73(2)
(1990), 270-273 (not available to us; the result is recorded by the next reference);
E. D. Demaine and R. A. Hearn, "Playing games with algorithms: algorithmic combinatorial game
theory", in Games of No Chance 3, MSRI Publications 56, Cambridge University Press (2009),
3-56, Section 5.10, arXiv:cs/0106019.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Prod
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PegSolitaire

/-!
# PEG SOLITAIRE (GENERALIZED HI-Q) is NP-complete

Demaine and Hearn (2009), Section 5.10, "Peg Solitaire (Hi-Q)": "Each move jumps a peg over
another peg (adjacent horizontally or vertically) to the opposite unoccupied position within the
cross, and removes the peg that was jumped over. The goal is to leave just a single peg". "A
natural generalization of peg solitaire is to consider pegs arranged in an `n × n` board and the
goal is to leave a single peg. Uehara and Iwata [UI90] proved that it is NP-complete to decide
whether such a puzzle is solvable."

INSTANCE: an `n × n` board with pegs in some of its holes.
QUESTION: is there a sequence of jumps that leaves exactly one peg?

Representation. The board is given row by row (`true` = peg), so the instance size is
proportional to its area. A position is the finset of holes `(row, column)` that carry a peg.
A jump moves a peg from `x` over a peg on the next hole `y` in a row or column to the next hole
`z` beyond it in the same direction, which must be an empty hole of the board, and removes the
peg on `y`. Unlike peg solitaire on graphs (`PegSolitaireOnGraphsWanted`), a jump cannot turn:
`x`, `y`, `z` are consecutive holes of one row or one column. Pegs stay on the board, since
every jump lands on a hole of the board.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the `n × n` board row by row, `true` for a hole with a peg. -/
abbrev PegSolitaireInstance := List (List Bool)

/-- The side length `n` of the board (its number of rows). -/
def size (i : PegSolitaireInstance) : ℕ := i.length

/-- The holes `x`, `y`, `z` are consecutive in one row or one column, in this order. -/
def InLine (x y z : ℕ × ℕ) : Prop :=
  (x.1 = y.1 ∧ y.1 = z.1 ∧
      ((x.2 + 1 = y.2 ∧ y.2 + 1 = z.2) ∨ (z.2 + 1 = y.2 ∧ y.2 + 1 = x.2))) ∨
    (x.2 = y.2 ∧ y.2 = z.2 ∧
      ((x.1 + 1 = y.1 ∧ y.1 + 1 = z.1) ∨ (z.1 + 1 = y.1 ∧ y.1 + 1 = x.1)))

/-- One jump on the `n × n` board from the position `P` to the position `Q`: the peg on `x`
jumps over the peg on `y` to the empty hole `z` of the board, and the peg on `y` is
removed. -/
def Jump (n : ℕ) (P Q : Finset (ℕ × ℕ)) : Prop :=
  ∃ x y z, InLine x y z ∧ z.1 < n ∧ z.2 < n ∧ x ∈ P ∧ y ∈ P ∧ z ∉ P ∧
    Q = insert z ((P.erase x).erase y)

/-- The initial position: the holes of the board that carry a peg. -/
def initial (i : PegSolitaireInstance) : Finset (ℕ × ℕ) :=
  (Finset.range (size i) ×ˢ Finset.range (size i)).filter fun x =>
    (i.getD x.1 []).getD x.2 false = true

/-- Well-formedness: the board is square, every row as long as the number of rows. -/
def WellFormed (i : PegSolitaireInstance) : Prop :=
  ∀ row ∈ i, row.length = size i

/-- Some sequence of jumps from the initial position leaves exactly one peg. -/
def PegSolitaireFeasible (i : PegSolitaireInstance) : Prop :=
  ∃ Q, Relation.ReflTransGen (Jump (size i)) (initial i) Q ∧ Q.card = 1

open Classical in
/-- PEG SOLITAIRE as a decision problem over bitstrings. -/
noncomputable def pegSolitaireDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PegSolitaireInstance) x with
  | some i => decide (WellFormed i ∧ PegSolitaireFeasible i)
  | none => false

/-- **PEG SOLITAIRE (GENERALIZED HI-Q) is NP-complete.** Source: Uehara and Iwata (1990), as
recorded by Demaine and Hearn (2009), Section 5.10. -/
public theorem_wanted pegSolitaire_npComplete :
    pegSolitaireDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pegSolitaireDec

end MetaMathlibExt.Complexity.NPComplete.PegSolitaire
