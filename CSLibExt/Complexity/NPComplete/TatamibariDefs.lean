/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TATAMIBARI: definitions

Source:
A. Adler, J. Bosboom, E. D. Demaine, M. L. Demaine, Q. C. Liu and J. Lynch, "Tatamibari is
NP-complete", 10th International Conference on Fun with Algorithms (FUN 2021), LIPIcs 157
(2020), 1:1-1:24, doi:10.4230/LIPIcs.FUN.2021.1 (arXiv:2003.08331).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Tatamibari

/-- An instance: the number of rows `m`, the number of columns `n`, and the list of clues; a
clue `(r, c, t)` sits in cell `(r, c)` and has kind `t`: `0` for `+`, `1` for `-`, `2` for
`|`. -/
abbrev TatamibariInstance := ℕ × ℕ × List (ℕ × ℕ × ℕ)

/-- Well-formedness of an instance: the grid has at least one row and one column, every clue
lies in the grid and has one of the three kinds, and no cell holds two clues. -/
def WellFormed (i : TatamibariInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ (∀ t ∈ i.2.2, t.1 < i.1 ∧ t.2.1 < i.2.1 ∧ t.2.2 < 3) ∧
    (i.2.2.map fun t => (t.1, t.2.1)).Nodup

/-- A grid-aligned rectangle `(r, c, h, w)` (top-left cell `(r, c)`, height `h`, width `w`)
contains the cell `(r', c')`. -/
def InRect (R : ℕ × ℕ × ℕ × ℕ) (r' c' : ℕ) : Prop :=
  R.1 ≤ r' ∧ r' < R.1 + R.2.2.1 ∧ R.2.1 ≤ c' ∧ c' < R.2.1 + R.2.2.2

/-- The lattice point `p` is a corner of the rectangle `(r, c, h, w)`. -/
def IsRectCorner (R : ℕ × ℕ × ℕ × ℕ) (p : ℕ × ℕ) : Prop :=
  (p.1 = R.1 ∨ p.1 = R.1 + R.2.2.1) ∧ (p.2 = R.2.1 ∨ p.2 = R.2.1 + R.2.2.2)

/-- A Tatamibari solution: rectangle `rect j = (r, c, h, w)` for each clue `j`, nonempty and
inside the grid, satisfying rules 1-7. -/
def TatamibariFeasible (i : TatamibariInstance) : Prop :=
  ∃ rect : ℕ → ℕ × ℕ × ℕ × ℕ,
    (∀ j < i.2.2.length, 0 < (rect j).2.2.1 ∧ 0 < (rect j).2.2.2 ∧
      (rect j).1 + (rect j).2.2.1 ≤ i.1 ∧ (rect j).2.1 + (rect j).2.2.2 ≤ i.2.1) ∧
    -- 1. disjoint
    (∀ j < i.2.2.length, ∀ j' < i.2.2.length, j ≠ j' →
      ∀ r c, ¬ (InRect (rect j) r c ∧ InRect (rect j') r c)) ∧
    -- 2. cover
    (∀ r < i.1, ∀ c < i.2.1, ∃ j < i.2.2.length, InRect (rect j) r c) ∧
    -- 3. rectangle `j` contains clue `j` and no other clue
    (∀ j < i.2.2.length, ∀ j' < i.2.2.length,
      (InRect (rect j) (i.2.2.getD j' (0, 0, 0)).1 (i.2.2.getD j' (0, 0, 0)).2.1 ↔ j' = j)) ∧
    -- 4-6. shapes
    (∀ j < i.2.2.length,
      ((i.2.2.getD j (0, 0, 0)).2.2 = 0 → (rect j).2.2.2 = (rect j).2.2.1) ∧
      ((i.2.2.getD j (0, 0, 0)).2.2 = 1 → (rect j).2.2.1 < (rect j).2.2.2) ∧
      ((i.2.2.getD j (0, 0, 0)).2.2 = 2 → (rect j).2.2.2 < (rect j).2.2.1)) ∧
    -- 7. no four rectangles share the same corner
    ¬ ∃ p : ℕ × ℕ, ∃ s : Finset ℕ, s.card = 4 ∧ (∀ j ∈ s, j < i.2.2.length) ∧
      ∀ j ∈ s, IsRectCorner (rect j) p

open Classical in
/-- TATAMIBARI as a decision problem over bitstrings. -/
noncomputable def tatamibariDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TatamibariInstance) x with
  | some i => decide (WellFormed i ∧ TatamibariFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Tatamibari
