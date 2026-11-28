/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HEBI: definitions

Source:
S. Kanehiro and Y. Takenaga, "Satogaeri, Hebi, and Suraromu are NP-complete", Proc. 3rd
International Conference on Applied Computing and Information Technology / 2nd International
Conference on Computational Science and Intelligence (ACIT-CSI 2015), IEEE (2015),
doi:10.1109/ACIT-CSI.2015.17;
puzzle rules: Nikoli Co., Ltd., "Hebi Ichigo", https://www.nikoli.co.jp/en/puzzles/hebi/ and
https://www.nikoli.co.jp/ja/puzzles/hebi/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Hebi

/-- A square `(b, v, d)`: black if `b = true`; a black square with `v ≥ 1` carries the number
`v - 1` and an arrow in direction `d` (`0` up, `1` right, `2` down, `3` left). -/
abbrev Square := Bool × ℕ × ℕ

/-- An instance: the grid row by row. -/
abbrev HebiInstance := List (List Square)

/-- The number of rows. -/
def rows (i : HebiInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : HebiInstance) : ℕ := (i.headD []).length

/-- The square at `x` (a black square without number off the grid). -/
def square (i : HebiInstance) (x : ℕ × ℕ) : Square := (i.getD x.1 []).getD x.2 (true, 0, 0)

/-- The square at `x` is a white square of the grid. -/
def white (i : HebiInstance) (x : ℕ × ℕ) : Bool :=
  decide (x.1 < rows i) && decide (x.2 < cols i) && !(square i x).1

/-- The square at distance `t` from `x` in direction `d`, if it has natural coordinates. -/
def shift (x : ℕ × ℕ) (d t : ℕ) : Option (ℕ × ℕ) :=
  if d = 0 then (if t ≤ x.1 then some (x.1 - t, x.2) else none)
  else if d = 1 then some (x.1, x.2 + t)
  else if d = 2 then some (x.1 + t, x.2)
  else if t ≤ x.2 then some (x.1, x.2 - t) else none

/-- The squares seen from `x` in direction `d`: those at distance `1, 2, …`, up to the next
black square or the rim. -/
def ray (i : HebiInstance) (x : ℕ × ℕ) (d : ℕ) : List (ℕ × ℕ) :=
  (((List.range (rows i + cols i)).map fun t => shift x d (t + 1)).takeWhile
    fun o => o.any (white i)).reduceOption

/-- Squares `x` and `y` share a side. -/
def Adjacent (x y : ℕ × ℕ) : Prop :=
  (x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2)) ∨ (x.2 = y.2 ∧ (x.1 + 1 = y.1 ∨ y.1 + 1 = x.1))

/-- The direction from square `p` to the square `q` next to it. -/
def dirTo (p q : ℕ × ℕ) : ℕ :=
  if q.1 + 1 = p.1 then 0 else if q.2 = p.2 + 1 then 1 else if q.1 = p.1 + 1 then 2 else 3

/-- The number in square `y` for the snakes `S`: `k + 1` if `y` is square `k` (counting from
`0` at the head) of a snake, `0` if no snake passes through `y`. -/
def numberAt (S : List (List (ℕ × ℕ))) (y : ℕ × ℕ) : ℕ :=
  (S.findSome? fun s => (s.findIdx? (· == y)).map (· + 1)).getD 0

/-- Well-formedness: at least one row and one column, rows of equal length, white squares
without number or arrow, and arrows pointing in one of the four directions. -/
def WellFormed (i : HebiInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ row ∈ i, ∀ q ∈ row, (q.1 = false → q.2 = (0, 0)) ∧ q.2.2 < 4

/-- The snakes `S` satisfy rules 1-4. -/
def Solves (i : HebiInstance) (S : List (List (ℕ × ℕ))) : Prop :=
  -- 1. each snake: five distinct white squares, `1` to `5` connected in order
  (∀ s ∈ S, s.length = 5 ∧ s.Nodup ∧ (∀ x ∈ s, white i x = true) ∧
    ∀ k < 4, Adjacent (s.getD k (0, 0)) (s.getD (k + 1) (0, 0))) ∧
  -- 2. different snakes share no square and no side
  (∀ a < S.length, ∀ b < S.length, a ≠ b → ∀ x ∈ S.getD a [], ∀ y ∈ S.getD b [],
    x ≠ y ∧ ¬ Adjacent x y) ∧
  -- 3. no other snake in a snake's direction of view
  (∀ a < S.length, ∀ y ∈ ray i ((S.getD a []).getD 0 (0, 0))
      (dirTo ((S.getD a []).getD 1 (0, 0)) ((S.getD a []).getD 0 (0, 0))),
    ∀ b < S.length, b ≠ a → y ∉ S.getD b []) ∧
  -- 4. a numbered black square shows the nearest number in the direction of its arrow
  ∀ r < rows i, ∀ c < cols i, (square i (r, c)).1 = true → 0 < (square i (r, c)).2.1 →
    (((ray i (r, c) (square i (r, c)).2.2).map (numberAt S)).find? (· ≠ 0)).getD 0 + 1 =
      (square i (r, c)).2.1

/-- Some nonempty list of snakes satisfies the rules. -/
def HebiFeasible (i : HebiInstance) : Prop :=
  ∃ S : List (List (ℕ × ℕ)), S ≠ [] ∧ Solves i S

open Classical in
/-- HEBI as a decision problem over bitstrings. -/
noncomputable def hebiDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HebiInstance) x with
  | some i => decide (WellFormed i ∧ HebiFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Hebi
