/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KPLUMBER: definitions

Source:
D. Král', V. Majerech, J. Sgall, T. Tichý and G. Woeginger, "It is tough to be a plumber",
Theoretical Computer Science 313 (2004), 473-484, doi:10.1016/j.tcs.2002.12.002.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KPlumber

/-- A tile: whether its north, east, south and west sides carry a pipe end. -/
abbrev Tile := Bool × Bool × Bool × Bool

/-- An instance: the number of rows `m`, the number of columns `n`, and the tiles row by row. -/
abbrev KPlumberInstance := ℕ × ℕ × List Tile

/-- Whether side `s` (`0` north, `1` east, `2` south, `3` west) of tile `t` carries a pipe
end. -/
def tileSide (t : Tile) : Fin 4 → Bool :=
  ![t.1, t.2.1, t.2.2.1, t.2.2.2]

/-- Whether side `s` carries a pipe end after `t` is rotated clockwise by `k` quarter turns: it
shows what side `s - k` showed. -/
def rotatedSide (t : Tile) (k s : Fin 4) : Bool :=
  tileSide t (s - k)

/-- The tile of row `r` and column `c`. -/
def tileAt (i : KPlumberInstance) (r c : ℕ) : Tile :=
  i.2.2.getD (r * i.2.1 + c) (false, false, false, false)

/-- Well-formedness of an instance: the grid has at least one row and one column, and lists
exactly `m * n` tiles. -/
def WellFormed (i : KPlumberInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ i.2.2.length = i.1 * i.2.1

/-- The rotation `rot r c` of every tile closes the pipe system: every pipe end of the tile in
row `r`, column `c` faces a neighbouring cell of the grid whose rotated tile has a pipe end on
the opposite side. -/
def Solves (i : KPlumberInstance) (rot : ℕ → ℕ → Fin 4) : Prop :=
  ∀ r < i.1, ∀ c < i.2.1,
    (rotatedSide (tileAt i r c) (rot r c) 0 = true →
      0 < r ∧ rotatedSide (tileAt i (r - 1) c) (rot (r - 1) c) 2 = true) ∧
    (rotatedSide (tileAt i r c) (rot r c) 1 = true →
      c + 1 < i.2.1 ∧ rotatedSide (tileAt i r (c + 1)) (rot r (c + 1)) 3 = true) ∧
    (rotatedSide (tileAt i r c) (rot r c) 2 = true →
      r + 1 < i.1 ∧ rotatedSide (tileAt i (r + 1) c) (rot (r + 1) c) 0 = true) ∧
    (rotatedSide (tileAt i r c) (rot r c) 3 = true →
      0 < c ∧ rotatedSide (tileAt i r (c - 1)) (rot r (c - 1)) 1 = true)

/-- Some rotation of the tiles leaves no open pipe end. -/
def KPlumberFeasible (i : KPlumberInstance) : Prop :=
  ∃ rot : ℕ → ℕ → Fin 4, Solves i rot

open Classical in
/-- KPLUMBER as a decision problem over bitstrings. -/
noncomputable def kPlumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KPlumberInstance) x with
  | some i => decide (WellFormed i ∧ KPlumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KPlumber
