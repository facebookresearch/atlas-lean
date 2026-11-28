/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SURAROMU: definitions

Source:
S. Kanehiro and Y. Takenaga, "Satogaeri, Hebi, and Suraromu are NP-complete", Proc. 3rd
International Conference on Applied Computing and Information Technology / 2nd International
Conference on Computational Science and Intelligence (ACIT-CSI 2015), IEEE (2015),
doi:10.1109/ACIT-CSI.2015.17;
puzzle rules: Nikoli Co., Ltd., "Suraromu", https://www.nikoli.co.jp/en/puzzles/suraromu/ and
https://www.nikoli.co.jp/ja/puzzles/suraromu/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Suraromu

/-- A gate `(r, c, ℓ, v, k)`: first cell `(r, c)`, length `ℓ`, vertical if `v` and horizontal
otherwise, and order number `k` (`0` = no number). -/
abbrev Gate := ℕ × ℕ × ℕ × Bool × ℕ

/-- An instance `(B, (r, c, s), G)`: the board `B` row by row (`true` = black cell), the circle
cell `(r, c)` with its number `s`, and the gates `G`. -/
abbrev SuraromuInstance := List (List Bool) × (ℕ × ℕ × ℕ) × List Gate

/-- The number of rows. -/
def rows (i : SuraromuInstance) : ℕ := i.1.length

/-- The number of columns (the length of the first row). -/
def cols (i : SuraromuInstance) : ℕ := (i.1.headD []).length

/-- Cell `x = (row, column)` is black (cells outside the board read as not black). -/
def IsBlack (i : SuraromuInstance) (x : ℕ × ℕ) : Prop := (i.1.getD x.1 []).getD x.2 false = true

/-- The circle cell. -/
def circleCell (i : SuraromuInstance) : ℕ × ℕ := (i.2.1.1, i.2.1.2.1)

/-- The number in the circle. -/
def circleNumber (i : SuraromuInstance) : ℕ := i.2.1.2.2

/-- The gates. -/
def gates (i : SuraromuInstance) : List Gate := i.2.2

/-- Cell `t` of gate `g` (counting from `0`). -/
def gateCell (g : Gate) (t : ℕ) : ℕ × ℕ :=
  if g.2.2.2.1 then (g.1 + t, g.2.1) else (g.1, g.2.1 + t)

/-- Cell `x` belongs to gate `g`. -/
def onGate (g : Gate) (x : ℕ × ℕ) : Bool :=
  (List.range g.2.2.1).any fun t => gateCell g t == x

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : SuraromuInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The indices of the gates containing cell `x`, in increasing order. -/
def gatesAt (i : SuraromuInstance) (x : Fin (rows i) × Fin (cols i)) : List ℕ :=
  (List.range (gates i).length).filter fun j =>
    onGate ((gates i).getD j default) ((x.1 : ℕ), (x.2 : ℕ))

/-- The gates a walk passes, in order: for each cell on it, the indices of the gates containing
that cell. -/
def crossings (i : SuraromuInstance) {u v : Fin (rows i) × Fin (cols i)}
    (w : (Grid i).Walk u v) : List ℕ :=
  w.support.flatMap (gatesAt i)

/-- Well-formedness: the board has at least one row and one column and rows of equal length; the
circle cell lies in the board, is white, and its number is the number of gates; each gate has
length at least `1`, its cells are white cells of the grid other than the circle cell, and the
cells just before its first cell and just after its last cell are black or outside the grid;
no gate is listed twice. -/
def WellFormed (i : SuraromuInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.1, row.length = cols i) ∧
  (circleCell i).1 < rows i ∧ (circleCell i).2 < cols i ∧ ¬ IsBlack i (circleCell i) ∧
  circleNumber i = (gates i).length ∧
  (∀ g ∈ gates i, 0 < g.2.2.1 ∧
    (∀ t < g.2.2.1, (gateCell g t).1 < rows i ∧ (gateCell g t).2 < cols i ∧
      ¬ IsBlack i (gateCell g t) ∧ gateCell g t ≠ circleCell i) ∧
    (if g.2.2.2.1 then g.1 = 0 ∨ IsBlack i (g.1 - 1, g.2.1)
      else g.2.1 = 0 ∨ IsBlack i (g.1, g.2.1 - 1)) ∧
    (rows i ≤ (gateCell g g.2.2.1).1 ∨ cols i ≤ (gateCell g g.2.2.1).2 ∨
      IsBlack i (gateCell g g.2.2.1))) ∧
  ((gates i).map fun g => (g.1, g.2.1, g.2.2.1, g.2.2.2.1)).Nodup

/-- The loop `c` from the circle cell satisfies rules 1, 2 and 4: it uses white cells only, it
passes each gate exactly once, and in one of the two directions the gate numbered `k` is the
`k`-th gate crossed. -/
def Solves (i : SuraromuInstance) {u : Fin (rows i) × Fin (cols i)} (c : (Grid i).Walk u u) :
    Prop :=
  (∀ x ∈ c.support, ¬ IsBlack i ((x.1 : ℕ), (x.2 : ℕ))) ∧
  (∀ j < (gates i).length, (crossings i c).count j = 1) ∧
  ∃ L ∈ [crossings i c, (crossings i c).reverse], ∀ j, ∀ h : j < (gates i).length,
    0 < ((gates i)[j]).2.2.2.2 → L[((gates i)[j]).2.2.2.2 - 1]? = some j

/-- Some cycle of the grid graph through the circle cell satisfies the rules. -/
def SuraromuFeasible (i : SuraromuInstance) : Prop :=
  ∃ u : Fin (rows i) × Fin (cols i), ((u.1 : ℕ), (u.2 : ℕ)) = circleCell i ∧
    ∃ c : (Grid i).Walk u u, c.IsCycle ∧ Solves i c

open Classical in
/-- SURAROMU as a decision problem over bitstrings. -/
noncomputable def suraromuDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SuraromuInstance) x with
  | some i => decide (WellFormed i ∧ SuraromuFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Suraromu
