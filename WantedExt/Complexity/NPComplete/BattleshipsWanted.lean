/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BATTLESHIPS is NP-complete

Source:
M. Sevenster, "Battleships as decision problem", ICGA Journal 27 (2004), 142-149,
doi:10.3233/ICG-2004-27303.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Set.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Battleships

/-!
# BATTLESHIPS is NP-complete

Sevenster (2004) treats an `m × n` Battleships puzzle as a tuple `⟨I, C, R, F⟩`: the initial
filling `I` of the grid, which marks each cell as `ship`, `water` or `?`; the column tally `C`
and the row tally `R`, which give a number for every column and every row; and the fleet `F`,
with "`F(k)` ships of ship-length `k`" (every ship has width `1`). A solution places the ships
so that

* C1: all ships in the fleet are put in the grid;
* C2: the indications in the initial grid are respected;
* C3: no two ships occupy adjacent (orthogonally or diagonally) squares;
* C4: the number of ship segments in column (row) `i` is equal to the `i`th value of the
  column (row) tally.

BATTLESHIPS asks: given a Battleships puzzle, does it have a solution?

Here the grid has `m = R.length` rows and `n = C.length` columns (rows and columns are numbered
from `0`). The fleet is the list `F` with `F[k] = F(k + 1)`, the number of ships of length
`k + 1`; lengths beyond the list have no ships. The cells of `I` other than `?` are listed as
`((row, column), b)`, with `b = true` for a ship segment and `b = false` for water. A ship is
placed by its first cell, an orientation (`true` for vertical, extending down; `false` for
horizontal, extending right) and its length; the ship segments of the solution are the cells
covered by the placed ships. C3 says that cells of two different placed ships differ by at least
two in some coordinate; in particular different ships share no cell.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **BATTLESHIPS is NP-complete.** Source: Sevenster (2004). -/
public theorem_wanted battleships_npComplete :
    battleshipsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L battleshipsDec

end MetaMathlibExt.Complexity.NPComplete.Battleships
