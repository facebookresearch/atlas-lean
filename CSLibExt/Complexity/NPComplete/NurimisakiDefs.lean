/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NURIMISAKI: definitions

Source:
C. Iwamoto and T. Ide, "Computational Complexity of Nurimisaki and Sashigane", IEICE
Transactions on Fundamentals of Electronics, Communications and Computer Sciences E103-A(10)
(2020), 1183-1192, doi:10.1587/transfun.2019DMP0002;
puzzle rules: Nikoli Co., Ltd., "Nurimisaki",
https://www.nikoli.co.jp/en/puzzles/nurimisaki/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nurimisaki

/-- An instance: the grid row by row, each cell `(circle, number)`; number `0` means none. -/
abbrev NurimisakiInstance := List (List (Bool × ℕ))

/-- The number of rows. -/
def rows (i : NurimisakiInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : NurimisakiInstance) : ℕ := (i.headD []).length

/-- The entry `(circle, number)` of cell `x`. -/
def clue (i : NurimisakiInstance) (x : Fin (rows i) × Fin (cols i)) : Bool × ℕ :=
  (i.getD x.1 []).getD x.2 (false, 0)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : NurimisakiInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, and numbers only in
circles. -/
def WellFormed (i : NurimisakiInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ row ∈ i, ∀ e ∈ row, e.1 = false → e.2 = 0

/-- Cell `x` is a Misaki for the filling `p` (`true` = black): it is white and exactly one of
the cells next to it is white. -/
def IsMisaki (i : NurimisakiInstance) (p : ℕ → ℕ → Bool) (x : Fin (rows i) × Fin (cols i)) :
    Prop :=
  p x.1 x.2 = false ∧ ∃! w, (Grid i).Adj x w ∧ p w.1 w.2 = false

/-- The point `(r, c)` of `ℤ × ℤ` is a white cell of the grid. -/
def WhiteAt (i : NurimisakiInstance) (p : ℕ → ℕ → Bool) (r c : ℤ) : Prop :=
  0 ≤ r ∧ r < rows i ∧ 0 ≤ c ∧ c < cols i ∧ p r.toNat c.toNat = false

/-- The filling `p` (`true` = black) satisfies rules 1-4. -/
def Solves (i : NurimisakiInstance) (p : ℕ → ℕ → Bool) : Prop :=
  -- 1. exactly the circled cells are Misaki cells (white, with one white neighbor)
  (∀ x, (clue i x).1 = true ↔ IsMisaki i p x) ∧
  -- 2. a circled number `k`: exactly `k` white cells in a straight line from the Misaki,
  -- through its white neighbor `w`, counting the Misaki
  (∀ x, (clue i x).1 = true → 0 < (clue i x).2 →
    ∃ w, (Grid i).Adj x w ∧ p w.1 w.2 = false ∧
      (∀ j < (clue i x).2,
        WhiteAt i p ((x.1 : ℕ) + j * (((w.1 : ℕ) : ℤ) - (x.1 : ℕ)))
          ((x.2 : ℕ) + j * (((w.2 : ℕ) : ℤ) - (x.2 : ℕ)))) ∧
      ¬ WhiteAt i p ((x.1 : ℕ) + (clue i x).2 * (((w.1 : ℕ) : ℤ) - (x.1 : ℕ)))
          ((x.2 : ℕ) + (clue i x).2 * (((w.2 : ℕ) : ℤ) - (x.2 : ℕ)))) ∧
  -- 3. the white cells form a continuous network
  ((Grid i).induce {x | p x.1 x.2 = false}).Connected ∧
  -- 4. no `2 × 2` square of black cells and none of white cells
  ∀ r c, r + 1 < rows i → c + 1 < cols i →
    ¬ (p r c = true ∧ p r (c + 1) = true ∧ p (r + 1) c = true ∧ p (r + 1) (c + 1) = true) ∧
    ¬ (p r c = false ∧ p r (c + 1) = false ∧ p (r + 1) c = false ∧ p (r + 1) (c + 1) = false)

/-- Some filling satisfies the rules. -/
def NurimisakiFeasible (i : NurimisakiInstance) : Prop :=
  ∃ p : ℕ → ℕ → Bool, Solves i p

open Classical in
/-- NURIMISAKI as a decision problem over bitstrings. -/
noncomputable def nurimisakiDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NurimisakiInstance) x with
  | some i => decide (WellFormed i ∧ NurimisakiFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Nurimisaki
