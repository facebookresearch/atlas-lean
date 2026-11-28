/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLICKOMANIA (SAMEGAME): definitions

Source:
T. C. Biedl, E. D. Demaine, M. L. Demaine, R. Fleischer, L. Jacobsen and J. I. Munro, "The
complexity of Clickomania", in R. J. Nowakowski (ed.), *More Games of No Chance*, MSRI
Publications 42, Cambridge University Press (2002), 389-404, doi:10.1017/9781316135167.029,
arXiv:cs/0107031.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Clickomania

/-- A board: its columns from left to right, each the list of the colors of its blocks from the
bottom up. -/
abbrev Board := List (List ℕ)

/-- The color of the block in column `p.1` and row `p.2` (rows counted from the bottom), if there
is a block there. -/
def colorAt (B : Board) (p : ℕ × ℕ) : Option ℕ := (B.getD p.1 [])[p.2]?

/-- `p` and `q` are blocks of the same color that share an edge. -/
def SameColorAdj (B : Board) (p q : ℕ × ℕ) : Prop :=
  (colorAt B p).isSome ∧ colorAt B p = colorAt B q ∧
    ((p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
      (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)))

/-- `q` lies in the group of the block `p`, the maximal connected monochromatic polyomino
containing `p`: it is reached from `p` through edge-adjacent blocks of the same color. -/
def InGroup (B : Board) (p q : ℕ × ℕ) : Prop :=
  Relation.ReflTransGen (SameColorAdj B) p q

open Classical in
/-- The board after the group of `p` is removed: in every column the remaining blocks settle
(fall straight down, keeping their order), and every column left without blocks is removed,
bringing its two sides together. -/
noncomputable def click (B : Board) (p : ℕ × ℕ) : Board :=
  ((List.range B.length).map fun c =>
    ((List.range (B.getD c []).length).filter fun r => decide (¬ InGroup B p (c, r))).map
      fun r => (B.getD c []).getD r 0).filter fun col => !col.isEmpty

/-- One move: select (click) a group of size at least two, i.e. a block `p` whose group contains
another block, and remove it. -/
def Move (B B' : Board) : Prop := ∃ p,
  (colorAt B p).isSome ∧ (∃ q, q ≠ p ∧ InGroup B p q) ∧ B' = click B p

/-- Well-formedness of an instance: the board is a full rectangle with at least one block, i.e.,
it has a column and every column has the same positive number of blocks. -/
def WellFormed (B : Board) : Prop :=
  B ≠ [] ∧ ∀ col ∈ B, col ≠ [] ∧ col.length = (B.headD []).length

/-- The puzzle is solvable: some sequence of moves removes all blocks. -/
def ClickomaniaFeasible (B : Board) : Prop :=
  Relation.ReflTransGen Move B []

open Classical in
/-- CLICKOMANIA as a decision problem over bitstrings. -/
noncomputable def clickomaniaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := Board) x with
  | some i => decide (WellFormed i ∧ ClickomaniaFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Clickomania
