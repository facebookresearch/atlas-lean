/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINESWEEPER CONSISTENCY: definitions

Source:
R. Kaye, "Minesweeper is NP-complete" (2000).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Minesweeper

/-- **Minesweeper instances.** A Minesweeper instance consists of a number of rows $R$, a number of
columns $C$ and a finite list of clues, where $R$ and $C$ are natural numbers and each clue is a
triple $(r, c, k)$ of natural numbers giving a row $r$, a column $c$ and the number $k$ shown. -/
abbrev MinesweeperInstance := ℕ × ℕ × List (ℕ × ℕ × ℕ)

/-- **Well-formed Minesweeper instances.** A Minesweeper instance with $R$ rows, $C$ columns and a
list of clues is well formed when every clue $(r, c, k)$ in the list satisfies $r < R$, $c < C$
and $k \le 8$. -/
def WellFormed (i : MinesweeperInstance) : Prop :=
  ∀ clue ∈ i.2.2, clue.1 < i.1 ∧ clue.2.1 < i.2.1 ∧ clue.2.2 ≤ 8

/-- **Feasible Minesweeper instances.** Index rows and columns by natural numbers, and call a cell
$(r', c') \ne (r, c)$ a neighbour of $(r, c)$ when $|r' - r| \le 1$ and $|c' - c| \le 1$. A
Minesweeper instance with $R$ rows, $C$ columns and a list of clues is feasible when there is a
finite set $M$ of cells $(r, c)$ with $r < R$ and $c < C$ (the mines) such that for every clue
$(r, c, k)$ in the list the cell $(r, c)$ is not in $M$ and exactly $k$ cells of $M$ are
neighbours of $(r, c)$. -/
def MinesweeperFeasible
    (i : MinesweeperInstance) : Prop :=
  ∃ mines : List (ℕ × ℕ), mines.Nodup ∧ (∀ m ∈ mines, m.1 < i.1 ∧ m.2 < i.2.1) ∧
    ∀ clue ∈ i.2.2, (clue.1, clue.2.1) ∉ mines ∧
      ((mines.filter (fun m => decide (m.1 ≤ clue.1 + 1) && decide (clue.1 ≤ m.1 + 1) &&
        decide (m.2 ≤ clue.2.1 + 1) && decide (clue.2.1 ≤ m.2 + 1) &&
        !(m == (clue.1, clue.2.1))))).length = clue.2.2

open Classical in
/-- **Minesweeper consistency as a decision problem.** The Minesweeper consistency decision
problem accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding,
to a Minesweeper instance that is well formed and feasible, that is, admits a mine placement
consistent with all of its clues. It rejects every bitstring that does not decode to a Minesweeper
instance. -/
noncomputable def minesweeperDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinesweeperInstance) x with
  | some i => decide (WellFormed i ∧ MinesweeperFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Minesweeper
