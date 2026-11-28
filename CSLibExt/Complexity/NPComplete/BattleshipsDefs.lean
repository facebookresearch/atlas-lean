/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BATTLESHIPS: definitions

Source:
M. Sevenster, "Battleships as decision problem", ICGA Journal 27 (2004), 142-149,
doi:10.3233/ICG-2004-27303.
-/
module

public import Mathlib.Data.Set.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Battleships

/-- An instance: row tally `R`, column tally `C`, fleet `F` (`F[k]` ships of length `k + 1`),
and the cells of the initial grid that are not `?`, as `((row, column), isShip)`. -/
abbrev BattleshipsInstance := List ℕ × List ℕ × List ℕ × List ((ℕ × ℕ) × Bool)

/-- A ship placement: first cell `(row, column)`, orientation (`true` for vertical), length. -/
abbrev Ship := (ℕ × ℕ) × Bool × ℕ

/-- The cells covered by a ship: `(row + t, column)` for vertical ships and `(row, column + t)`
for horizontal ships, for `t` below the length. -/
def shipCells (s : Ship) : Set (ℕ × ℕ) :=
  {p | ∃ t < s.2.2, p = if s.2.1 then (s.1.1 + t, s.1.2) else (s.1.1, s.1.2 + t)}

/-- Two cells are equal or adjacent, orthogonally or diagonally: they differ by at most one in
each coordinate. -/
def Near (p q : ℕ × ℕ) : Prop :=
  p.1 ≤ q.1 + 1 ∧ q.1 ≤ p.1 + 1 ∧ p.2 ≤ q.2 + 1 ∧ q.2 ≤ p.2 + 1

/-- A cell holds a ship segment: some placed ship covers it. -/
def Occupied (P : List Ship) (p : ℕ × ℕ) : Prop :=
  ∃ s ∈ P, p ∈ shipCells s

/-- Well-formedness of an instance: the given cells lie in the `R.length × C.length` grid and no
cell is given twice. -/
def WellFormed (i : BattleshipsInstance) : Prop :=
  (∀ c ∈ i.2.2.2, c.1.1 < i.1.length ∧ c.1.2 < i.2.1.length) ∧
    (i.2.2.2.map Prod.fst).Nodup

/-- The puzzle has a solution: a list of placed ships satisfying C1-C4. -/
def BattleshipsFeasible (i : BattleshipsInstance) : Prop :=
  ∃ P : List Ship,
    -- C1: the placed ships are exactly the fleet, each inside the grid
    (∀ k, P.countP (fun s => s.2.2 = k + 1) = i.2.2.1.getD k 0) ∧
    (∀ s ∈ P, 0 < s.2.2 ∧ ∀ p ∈ shipCells s, p.1 < i.1.length ∧ p.2 < i.2.1.length) ∧
    -- C2: the initial grid is respected
    (∀ c ∈ i.2.2.2, (Occupied P c.1 ↔ c.2 = true)) ∧
    -- C3: no two ships occupy adjacent (orthogonally or diagonally) squares
    (∀ a b : Fin P.length, a ≠ b →
      ∀ p ∈ shipCells P[a], ∀ q ∈ shipCells P[b], ¬ Near p q) ∧
    -- C4: row and column tallies
    (∀ r : Fin i.1.length, {c | c < i.2.1.length ∧ Occupied P (r, c)}.ncard = i.1[r]) ∧
    ∀ c : Fin i.2.1.length, {r | r < i.1.length ∧ Occupied P (r, c)}.ncard = i.2.1[c]

open Classical in
/-- BATTLESHIPS as a decision problem over bitstrings. -/
noncomputable def battleshipsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BattleshipsInstance) x with
  | some i => decide (WellFormed i ∧ BattleshipsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Battleships
