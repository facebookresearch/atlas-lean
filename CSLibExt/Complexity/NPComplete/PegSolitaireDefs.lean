/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PEG SOLITAIRE (GENERALIZED HI-Q): definitions

Source:
R. Uehara and S. Iwata, "Generalized Hi-Q is NP-complete", Transactions of the IEICE E73(2)
(1990), 270-273 (not available to us; the result is recorded by the next reference);
E. D. Demaine and R. A. Hearn, "Playing games with algorithms: algorithmic combinatorial game
theory", in Games of No Chance 3, MSRI Publications 56, Cambridge University Press (2009),
3-56, Section 5.10, arXiv:cs/0106019.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Prod
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PegSolitaire

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

end MetaMathlibExt.Complexity.NPComplete.PegSolitaire
