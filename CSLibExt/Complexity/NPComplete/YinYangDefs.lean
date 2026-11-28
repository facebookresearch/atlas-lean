/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# YIN-YANG: definitions

Source:
E. D. Demaine, J. Lynch, M. Rudoy and Y. Uno, "Yin-Yang puzzles are NP-complete", Proceedings
of the 33rd Canadian Conference on Computational Geometry (CCCG 2021), arXiv:2106.15585.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.YinYang

/-- An instance: the width `w` and the rows of cell entries (`h` rows of `w` entries), `0` for
an empty cell, `1` for a black circle and `2` for a white circle. -/
abbrev YinYangInstance := ℕ × List (List ℕ)

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : YinYangInstance) := Fin i.2.length × Fin i.1

/-- Orthogonal adjacency of cells: the grid graph, the box product of two path graphs. -/
abbrev gridGraph (i : YinYangInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph i.2.length □ SimpleGraph.pathGraph i.1

/-- The entry of a cell. -/
def entry (i : YinYangInstance) (u : Cell i) : ℕ :=
  (i.2.getD u.1 []).getD u.2 0

/-- Well-formedness of an instance: every row has `w` entries, each `0`, `1` or `2`. -/
def WellFormed (i : YinYangInstance) : Prop :=
  ∀ row ∈ i.2, row.length = i.1 ∧ ∀ e ∈ row, e ≤ 2

/-- The puzzle has a solution: a coloring `black` of the cells (`true` for black) that keeps
the given circles, whose black cells and whose white cells each induce a connected subgraph of
the grid, and with no `2 × 2` square of four cells of one color (the square with top left cell
`u` consists of `u` and its neighbors below, to the right, and diagonally below right). -/
def YinYangFeasible (i : YinYangInstance) : Prop :=
  ∃ black : Cell i → Bool,
    (∀ u, entry i u = 1 → black u = true) ∧ (∀ u, entry i u = 2 → black u = false) ∧
    ((gridGraph i).induce {u | black u = true}).Connected ∧
    ((gridGraph i).induce {u | black u = false}).Connected ∧
    ∀ u : Cell i, ∀ (h₁ : (u.1 : ℕ) + 1 < i.2.length) (h₂ : (u.2 : ℕ) + 1 < i.1),
      ¬ (black (⟨u.1 + 1, h₁⟩, u.2) = black u ∧ black (u.1, ⟨u.2 + 1, h₂⟩) = black u ∧
        black (⟨u.1 + 1, h₁⟩, ⟨u.2 + 1, h₂⟩) = black u)

open Classical in
/-- YIN-YANG as a decision problem over bitstrings. -/
noncomputable def yinYangDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := YinYangInstance) x with
  | some i => decide (WellFormed i ∧ YinYangFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.YinYang
