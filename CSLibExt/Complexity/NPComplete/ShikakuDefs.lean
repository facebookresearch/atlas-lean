/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHIKAKU: definitions

Source:
Y. Takenaga, S. Aoyagi, S. Iwata and T. Kasai, "Shikaku and ripple effect are NP-complete",
Congressus Numerantium 216 (2013), 119-127, MR3220078;
puzzle rules: Nikoli Co., Ltd., "Shikaku", https://www.nikoli.co.jp/en/puzzles/shikaku/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Shikaku

/-- An instance: the grid row by row, `0` for an empty cell and `k ≥ 1` for a cell containing
`k`. -/
abbrev ShikakuInstance := List (List ℕ)

/-- The number of rows `m`. -/
def rows (i : ShikakuInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
def cols (i : ShikakuInstance) : ℕ := (i.headD []).length

/-- The number in cell `x` (`0` if empty). -/
def number (i : ShikakuInstance) (x : ℕ × ℕ) : ℕ := (i.getD x.1 []).getD x.2 0

/-- A rectangle `(r, c, h, w)`: top-left cell `(r, c)`, height `h`, width `w`. -/
abbrev Rect := ℕ × ℕ × ℕ × ℕ

/-- The cells `(r + a, c + b)`, `a < h`, `b < w`, of the rectangle `(r, c, h, w)`. -/
def cells (q : Rect) : List (ℕ × ℕ) :=
  (List.range q.2.2.1).flatMap fun a => (List.range q.2.2.2).map fun b => (q.1 + a, q.2.1 + b)

/-- Well-formedness: at least one row and one column, and rows of equal length. -/
def WellFormed (i : ShikakuInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ ∀ row ∈ i, row.length = cols i

/-- Some list of rectangles inside the grid divides it (every cell lies in exactly one
rectangle), and every rectangle contains exactly one number, equal to its number of cells. -/
def ShikakuFeasible (i : ShikakuInstance) : Prop :=
  ∃ R : List Rect,
    (∀ q ∈ R, 0 < q.2.2.1 ∧ 0 < q.2.2.2 ∧ q.1 + q.2.2.1 ≤ rows i ∧ q.2.1 + q.2.2.2 ≤ cols i) ∧
    (∀ r < rows i, ∀ c < cols i, (R.filter fun q => (r, c) ∈ cells q).length = 1) ∧
    ∀ q ∈ R, ((cells q).filter fun x => number i x ≠ 0).length = 1 ∧
      ∀ x ∈ cells q, number i x ≠ 0 → number i x = q.2.2.1 * q.2.2.2

open Classical in
/-- SHIKAKU as a decision problem over bitstrings. -/
noncomputable def shikakuDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShikakuInstance) x with
  | some i => decide (WellFormed i ∧ ShikakuFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Shikaku
