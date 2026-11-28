/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MOON-OR-SUN: definitions

Source:
C. Iwamoto and T. Ide, "Moon-or-Sun, Nagareru, and Nurimeizu are NP-complete",
IEICE Transactions on Fundamentals of Electronics, Communications and Computer Sciences
E105-A(9) (2022), 1187-1194, doi:10.1587/transfun.2021DMP0006;
puzzle rules: Nikoli Co., Ltd., "Moon-or-Sun",
https://www.nikoli.co.jp/en/puzzles/moon_or_sun/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MoonOrSun

/-- An instance: the number of rooms `R`, and the grid row by row, each cell `(room, mark)`
with mark `0` (empty), `1` (moon) or `2` (sun). -/
abbrev MoonOrSunInstance := ℕ × List (List (ℕ × ℕ))

/-- The number of rows. -/
def rows (i : MoonOrSunInstance) : ℕ := i.2.length

/-- The number of columns (the length of the first row). -/
def cols (i : MoonOrSunInstance) : ℕ := (i.2.headD []).length

/-- The entry `(room, mark)` of cell `x`. -/
def cell (i : MoonOrSunInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ × ℕ :=
  (i.2.getD x.1 []).getD x.2 (0, 0)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : MoonOrSunInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, room indices below
`R`, marks at most `2`, and every room a nonempty connected set of cells. -/
def WellFormed (i : MoonOrSunInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.2, row.length = cols i) ∧
    (∀ row ∈ i.2, ∀ e ∈ row, e.1 < i.1 ∧ e.2 ≤ 2) ∧
    ∀ k < i.1, ((Grid i).induce {x | (cell i x).1 = k}).Connected

/-- The cycle `c` and the room types `τ` (`true` = moon) satisfy rules 2-4. -/
def Solves (i : MoonOrSunInstance) {u : Fin (rows i) × Fin (cols i)} (c : (Grid i).Walk u u)
    (τ : ℕ → Bool) : Prop :=
  -- 2. the loop goes through every room, and enters each room at most once
  (∀ k < i.1, ∃ v ∈ c.support, (cell i v).1 = k) ∧
  (∀ k < i.1, (c.darts.filter fun d =>
      (cell i d.snd).1 = k ∧ (cell i d.fst).1 ≠ k).length ≤ 1) ∧
  -- 3. a moon cell is on the loop iff its room is a moon room; likewise for suns
  (∀ x, (cell i x).2 = 1 → (x ∈ c.support ↔ τ (cell i x).1 = true)) ∧
  (∀ x, (cell i x).2 = 2 → (x ∈ c.support ↔ τ (cell i x).1 = false)) ∧
  -- 4. moving into the next room changes the type
  ∀ d ∈ c.darts, (cell i d.fst).1 ≠ (cell i d.snd).1 →
    τ (cell i d.fst).1 ≠ τ (cell i d.snd).1

/-- Some cycle of the grid graph, with some room types, satisfies the rules. -/
def MoonOrSunFeasible (i : MoonOrSunInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCycle ∧ ∃ τ : ℕ → Bool, Solves i c τ

open Classical in
/-- MOON-OR-SUN as a decision problem over bitstrings. -/
noncomputable def moonOrSunDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MoonOrSunInstance) x with
  | some i => decide (WellFormed i ∧ MoonOrSunFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MoonOrSun
