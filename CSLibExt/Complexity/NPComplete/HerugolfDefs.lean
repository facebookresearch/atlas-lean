/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HERUGOLF: definitions

Source:
C. Iwamoto, M. Haruishi and T. Ibusuki, "Computational complexity of Herugolf and Makaro",
IEICE Transactions on Fundamentals of Electronics, Communications and Computer Sciences E102-A(9)
(2019), 1118-1125, doi:10.1587/transfun.E102.A.1118;
Nikoli, Herugolf rules, https://www.nikoli.co.jp/en/puzzles/herugolf/ (Japanese:
https://www.nikoli.co.jp/ja/puzzles/herugolf/).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Herugolf

/-- An instance: the board, as a list of rows of cell codes (`0` empty, `1` hole, `2` water,
`k + 2` a ball with number `k`). -/
abbrev HerugolfInstance := List (List ℕ)

/-- The board width `w`: the length of the first row. -/
def width (i : HerugolfInstance) : ℕ := (i.headD []).length

/-- The code of cell `(x, y)` (column `x`, row `y`). -/
def code (i : HerugolfInstance) (c : ℕ × ℕ) : ℕ := (i.getD c.2 []).getD c.1 0

/-- The cells of the board, row by row. -/
def cells (i : HerugolfInstance) : List (ℕ × ℕ) :=
  (List.range i.length).flatMap fun y => (List.range (width i)).map fun x => (x, y)

/-- The cells holding a ball. -/
def balls (i : HerugolfInstance) : List (ℕ × ℕ) := (cells i).filter fun c => 3 ≤ code i c

/-- The hole cells. -/
def holes (i : HerugolfInstance) : List (ℕ × ℕ) := (cells i).filter fun c => code i c = 1

/-- The water-hazard cells. -/
def water (i : HerugolfInstance) : List (ℕ × ℕ) := (cells i).filter fun c => code i c = 2

/-- A cell as an integer point. -/
def cell (p : ℕ × ℕ) : ℤ × ℤ := ((p.1 : ℤ), (p.2 : ℤ))

/-- The four shot directions: right, left, down, up. -/
def dir : Fin 4 → ℤ × ℤ := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- The cell where a shot of length `ℓ` from `p` in direction `d` stops. -/
def step (p : ℤ × ℤ) (ℓ : ℕ) (d : Fin 4) : ℤ × ℤ := p + (ℓ : ℤ) • dir d

/-- The cells covered by the arrow of a shot of length `ℓ` from `p` in direction `d`:
`p + d, …, p + ℓ • d`. -/
def shot (p : ℤ × ℤ) (ℓ : ℕ) (d : Fin 4) : List (ℤ × ℤ) :=
  (List.range ℓ).map fun t => p + ((t : ℤ) + 1) • dir d

/-- The stopping cells of the shots `ds` of a ball at `p` whose next shot has length `ℓ`. -/
def stops : ℤ × ℤ → ℕ → List (Fin 4) → List (ℤ × ℤ)
  | _, _, [] => []
  | p, ℓ, d :: ds => step p ℓ d :: stops (step p ℓ d) (ℓ - 1) ds

/-- The cells covered by the arrows of the shots `ds` of a ball at `p` whose next shot has
length `ℓ`, in order. -/
def path : ℤ × ℤ → ℕ → List (Fin 4) → List (ℤ × ℤ)
  | _, _, [] => []
  | p, ℓ, d :: ds => shot p ℓ d ++ path (step p ℓ d) (ℓ - 1) ds

/-- The cell is on the `w × h` board. -/
def InGrid (i : HerugolfInstance) (q : ℤ × ℤ) : Prop :=
  0 ≤ q.1 ∧ q.1 < width i ∧ 0 ≤ q.2 ∧ q.2 < i.length

/-- The ball at cell `c` with shots `ds` follows the rules: between `1` and `k` shots (`k` its
number), all covered cells on the board, no stop on water, the final stop a hole, and no covered
cell before the final stop a hole or a ball's cell. -/
def LegalShots (i : HerugolfInstance) (c : ℕ × ℕ) (ds : List (Fin 4)) : Prop :=
  1 ≤ ds.length ∧ ds.length ≤ code i c - 2 ∧
    (∀ q ∈ path (cell c) (code i c - 2) ds, InGrid i q) ∧
    (∀ q ∈ stops (cell c) (code i c - 2) ds, q ∉ (water i).map cell) ∧
    (∃ q ∈ holes i, (stops (cell c) (code i c - 2) ds).getLast? = some (cell q)) ∧
    ∀ q ∈ (path (cell c) (code i c - 2) ds).dropLast,
      q ∉ (holes i).map cell ∧ q ∉ (balls i).map cell

/-- Well-formedness of an instance: the board has at least one row and one column, and it is
rectangular (all rows have the same length). -/
def WellFormed (i : HerugolfInstance) : Prop :=
  0 < i.length ∧ 0 < width i ∧ ∀ r ∈ i, r.length = width i

/-- Some shot lists move every ball legally into a hole, with all start cells and covered cells
pairwise distinct and every hole reached. -/
def HerugolfFeasible (i : HerugolfInstance) : Prop :=
  ∃ plan : ℕ × ℕ → List (Fin 4),
    (∀ c ∈ balls i, LegalShots i c (plan c)) ∧
    ((balls i).flatMap fun c => cell c :: path (cell c) (code i c - 2) (plan c)).Nodup ∧
    ∀ q ∈ holes i, ∃ c ∈ balls i,
      (stops (cell c) (code i c - 2) (plan c)).getLast? = some (cell q)

open Classical in
/-- HERUGOLF as a decision problem over bitstrings. -/
noncomputable def herugolfDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HerugolfInstance) x with
  | some i => decide (WellFormed i ∧ HerugolfFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Herugolf
