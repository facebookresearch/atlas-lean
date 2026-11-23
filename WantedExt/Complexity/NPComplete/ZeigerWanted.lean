/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZEIGER is NP-complete

Source:
S. Ruangwises, "NP-completeness and physical zero-knowledge proofs for Zeiger", in WALCOM:
Algorithms and Computation, Lecture Notes in Computer Science (2025), 312-325,
doi:10.1007/978-981-96-2845-2_20 (arXiv:2409.14308).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Zeiger

/-!
# ZEIGER is NP-complete

INSTANCE: a rectangular grid, each cell having an arrow pointing in a horizontal or vertical
direction; some cells also contain a positive integer.
QUESTION: can a positive integer be filled into every unnumbered cell so that the integer in each
cell equals the number of different integers in all cells along the direction the arrow in that
cell points to?

The grid is given explicitly, row by row: each cell is `(d, a)` with arrow `d` (`0` up, `1`
right, `2` down, `3` left) and `a = 0` (no number) or the given positive integer `a`. The cells
along the arrow of cell `(r, c)` are the cells strictly beyond it in that direction, up to the
edge of the grid (`Ray`): for an up arrow the cells `(r', c)` with `r' < r`, and so on. A
solution is a positive integer `v x` in every cell, equal to the given integer where there is
one, such that `v x` is the number of distinct values of `v` on the ray of `x`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the grid row by row; each cell is `(d, a)`, arrow `d` (`0` up, `1` right,
`2` down, `3` left) and `a = 0` (no number) or the given integer `a`. -/
abbrev ZeigerInstance := List (List (ℕ × ℕ))

/-- The number of rows. -/
abbrev rows (i : ZeigerInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
abbrev cols (i : ZeigerInstance) : ℕ := (i.headD []).length

/-- The content `(d, a)` of cell `(r, c)`. -/
def cell (i : ZeigerInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ × ℕ :=
  (i.getD x.1 []).getD x.2 (0, 0)

/-- The cell `y` lies along the arrow of cell `x`: strictly beyond `x` in the arrow's direction. -/
def Ray (i : ZeigerInstance) (x y : Fin (rows i) × Fin (cols i)) : Prop :=
  ((cell i x).1 = 0 ∧ y.2 = x.2 ∧ y.1 < x.1) ∨ ((cell i x).1 = 1 ∧ y.1 = x.1 ∧ x.2 < y.2) ∨
    ((cell i x).1 = 2 ∧ y.2 = x.2 ∧ x.1 < y.1) ∨ ((cell i x).1 = 3 ∧ y.1 = x.1 ∧ y.2 < x.2)

/-- Well-formedness of an instance: the grid has at least one row and one column, all rows have
the same length (the grid is rectangular), and every arrow is one of the four directions. -/
def WellFormed (i : ZeigerInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧ ∀ row ∈ i, ∀ e ∈ row, e.1 < 4

open Classical in
/-- Some positive integers `v x`, equal to the given integers where present, satisfy: `v x` is the
number of distinct values of `v` on the cells along the arrow of `x`. -/
def ZeigerFeasible (i : ZeigerInstance) : Prop :=
  ∃ v : Fin (rows i) × Fin (cols i) → ℕ, (∀ x, 0 < v x) ∧
    (∀ x, (cell i x).2 ≠ 0 → v x = (cell i x).2) ∧
    ∀ x, v x = ((Finset.univ.filter fun y => Ray i x y).image v).card

open Classical in
/-- ZEIGER as a decision problem over bitstrings. -/
noncomputable def zeigerDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ZeigerInstance) x with
  | some i => decide (WellFormed i ∧ ZeigerFeasible i)
  | none => false

/-- **ZEIGER is NP-complete.** Source: Ruangwises (2025). -/
public theorem_wanted zeiger_npComplete :
    zeigerDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zeigerDec

end MetaMathlibExt.Complexity.NPComplete.Zeiger
