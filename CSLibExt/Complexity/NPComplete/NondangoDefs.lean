/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NONDANGO: definitions

Source:
S. Ruangwises, "Nondango is NP-complete", arXiv:2310.11447 (2023),
https://arxiv.org/abs/2310.11447.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nondango

/-- An instance: the number of regions, and the rows of the grid, top to bottom; the entry of a
cell is `(region, circle)`. -/
abbrev NondangoInstance := ℕ × List (List (ℕ × Bool))

/-- The number of rows. -/
abbrev rows (i : NondangoInstance) : ℕ := i.2.length

/-- The number of columns, the length of the first row. -/
abbrev cols (i : NondangoInstance) : ℕ := (i.2.headD []).length

/-- The cells of the grid. -/
abbrev Cell (i : NondangoInstance) := Fin (rows i) × Fin (cols i)

/-- The entry `(region, circle)` of the cell in row `p.1` and column `p.2`. -/
def entry (i : NondangoInstance) (p : Cell i) : ℕ × Bool :=
  (i.2.getD p.1 []).getD p.2 (0, false)

/-- The grid graph: cells are adjacent when they share a side. -/
abbrev grid (h w : ℕ) : SimpleGraph (Fin h × Fin w) :=
  SimpleGraph.pathGraph h □ SimpleGraph.pathGraph w

/-- Well-formedness of an instance: at least one row and one column, every row of the same
length, region indices below the number of regions, and every region connected. -/
def WellFormed (i : NondangoInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.2, row.length = cols i) ∧
    (∀ row ∈ i.2, ∀ e ∈ row, e.1 < i.1) ∧
    ∀ k < i.1, ((grid (rows i) (cols i)).induce {p | (entry i p).1 = k}).Connected

/-- The cells `p`, `q`, `s` are three consecutive cells of a row, a column, or a diagonal. -/
def Consecutive {h w : ℕ} (p q s : Fin h × Fin w) : Prop :=
  (p.1 = q.1 ∧ q.1 = s.1 ∧ (p.2 : ℕ) + 1 = q.2 ∧ (q.2 : ℕ) + 1 = s.2) ∨
  (p.2 = q.2 ∧ q.2 = s.2 ∧ (p.1 : ℕ) + 1 = q.1 ∧ (q.1 : ℕ) + 1 = s.1) ∨
  ((p.1 : ℕ) + 1 = q.1 ∧ (q.1 : ℕ) + 1 = s.1 ∧ (p.2 : ℕ) + 1 = q.2 ∧ (q.2 : ℕ) + 1 = s.2) ∨
  ((p.1 : ℕ) + 1 = q.1 ∧ (q.1 : ℕ) + 1 = s.1 ∧ (q.2 : ℕ) + 1 = p.2 ∧ (s.2 : ℕ) + 1 = q.2)

/-- Coloring the circles in `B` black (and the other circles white) satisfies the rules: only
circles are colored, every region contains exactly one black circle, and no three consecutive
circles have the same color. -/
def Solves (i : NondangoInstance) (B : Set (Cell i)) : Prop :=
  (∀ p ∈ B, (entry i p).2 = true) ∧
  (∀ k < i.1, {p ∈ B | (entry i p).1 = k}.ncard = 1) ∧
  ∀ p q s, Consecutive p q s → (entry i p).2 = true → (entry i q).2 = true →
    (entry i s).2 = true →
      ¬ ((p ∈ B ∧ q ∈ B ∧ s ∈ B) ∨ (p ∉ B ∧ q ∉ B ∧ s ∉ B))

/-- Some coloring satisfies the rules. -/
def NondangoFeasible (i : NondangoInstance) : Prop :=
  ∃ B : Set (Cell i), Solves i B

open Classical in
/-- NONDANGO as a decision problem over bitstrings. -/
noncomputable def nondangoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NondangoInstance) x with
  | some i => decide (WellFormed i ∧ NondangoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Nondango
