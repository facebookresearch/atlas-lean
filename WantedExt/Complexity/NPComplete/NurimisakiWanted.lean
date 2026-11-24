/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NURIMISAKI is NP-complete

Source:
C. Iwamoto and T. Ide, "Computational Complexity of Nurimisaki and Sashigane", IEICE
Transactions on Fundamentals of Electronics, Communications and Computer Sciences E103-A(10)
(2020), 1183-1192, doi:10.1587/transfun.2019DMP0002;
puzzle rules: Nikoli Co., Ltd., "Nurimisaki",
https://www.nikoli.co.jp/en/puzzles/nurimisaki/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nurimisaki

/-!
# NURIMISAKI is NP-complete

Nurimisaki (Nikoli) is played on a rectangular grid; some cells contain a circle, possibly with
a number in it. Nikoli's rules: fill in the cells (black or white) under the following rules.
1. Cells with a circle remain white and must be a "Misaki" (promontory), while cells without a
   circle cannot be a Misaki. A white Misaki cell has only one of the cells next to it
   remaining white and the rest have to be black (vertically and horizontally).
2. The numbers in the circles indicate how many white cells form a straight line from the
   Misaki cell. At the cells with empty circles, any number of white cells may form a straight
   line.
3. White cells have to form a continuous network.
4. Neither black cells nor white cells can be linked to be a `2 × 2` square or larger.

INSTANCE: a rectangular grid with some cells containing a circle, possibly numbered.
QUESTION: can the cells be filled so that rules 1-4 hold? (Iwamoto and Ide 2020 prove this
NP-complete.)

The grid is given row by row: entry `j` of row `k` is `(circle, number)` for the cell in row `k`
and column `j`: `(false, 0)` for a cell without a circle, `(true, 0)` for an empty circle and
`(true, k)` with `k ≥ 1` for a circle with number `k`. `WellFormed` requires `m, n ≥ 1` rows and
columns, rows of equal length, and no number outside a circle. A filling is a function
`ℕ → ℕ → Bool` (`true` = black) read on the grid. Cells are `Fin m × Fin n`, next to each other
(vertically and horizontally) when adjacent in Mathlib's grid graph `pathGraph m □ pathGraph n`.

A Misaki is a white cell with exactly one white neighbor. Rule 2: the straight line runs from
the Misaki through its white neighbor `w`; a number `k` means that the `k` cells at distances
`0, …, k - 1` from the Misaki in that direction are white (the Misaki is the first of them) and
the cell at distance `k` is black or outside the grid. Counting the Misaki itself matches
Nikoli's sample solution, where a circled `4` heads a line of four white cells. Rule 3 is
`SimpleGraph.Connected` of the subgraph the grid graph induces on the white cells, so some cell
is white.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **NURIMISAKI is NP-complete.** Source: Iwamoto and Ide (2020). -/
public theorem_wanted nurimisaki_npComplete :
    nurimisakiDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nurimisakiDec

end MetaMathlibExt.Complexity.NPComplete.Nurimisaki
