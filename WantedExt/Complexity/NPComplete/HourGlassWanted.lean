/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THE HOUR-GLASS is NP-complete

Source:
H. Petersen, "The Complexity of Some Combinatorial Puzzles", arXiv:1507.08690 (2015), Theorem 2
("Generalized Hour-Glass is complete in NP").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HourGlass

/-!
# THE HOUR-GLASS is NP-complete

Petersen: "The Hour-Glass consists of two triangular shapes containing numbers and a target sum.
The goal is to find a path from the first row to the last row such that the numbers traversed
add up to the target sum. Each step moves diagonally down the structure." The generalized puzzle
has arbitrary size and arbitrary numbers, and asks whether a solution exists.

INSTANCE: a positive integer `m`, an hour-glass of `2m - 1` rows of natural numbers whose widths
are `m, m - 1, ..., 2, 1, 2, ..., m - 1, m` (an inverted triangle on top of an upright one, meeting
in a single cell), and a target sum `t`.
QUESTION: is there a path that starts in a cell of the first row, moves in each step diagonally
down to an adjacent cell of the next row, ends in the last row, and whose numbers add up to `t`?

Rows are numbered `0, ..., 2m - 2` and the cells of a row `0, 1, ...` from the left; row `r` has
width `m - r` for `r < m` and `r + 2 - m` for `r ≥ m`. A cell `j` of a row of width `w` lies
between the cells `j` and `j + 1` of an adjacent row of width `w + 1`, so a diagonal step down
from cell `j` goes to cell `j - 1` or `j` of the next row while the rows shrink (`r + 1 < m`), and
to cell `j` or `j + 1` while they grow. A path is a choice of a cell `p r` in every row `r`. The
numbers are in binary encoding; with bounded numbers the problem is easier (Petersen, Section 3).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the width `m` of the first row, the rows of numbers (top to bottom, each left to
right), and the target sum `t`. -/
abbrev HourGlassInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: `0 < m`, there are `2m - 1` rows, and row `r` has width
`m - r` for `r < m` and `r + 2 - m` otherwise. -/
def WellFormed (i : HourGlassInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = 2 * i.1 - 1 ∧
    ∀ r < i.2.1.length,
      (i.2.1.getD r []).length = if r < i.1 then i.1 - r else r + 2 - i.1

/-- A path `p` (cell `p r` in row `r`) moving diagonally down from the first row to the last
row, whose numbers add up to `t`. -/
def HourGlassFeasible (i : HourGlassInstance) : Prop :=
  ∃ p : ℕ → ℕ, (∀ r < i.2.1.length, p r < (i.2.1.getD r []).length) ∧
    (∀ r, r + 1 < i.2.1.length →
      if r + 1 < i.1 then p (r + 1) + 1 = p r ∨ p (r + 1) = p r
      else p (r + 1) = p r ∨ p (r + 1) = p r + 1) ∧
    ∑ r ∈ Finset.range i.2.1.length, (i.2.1.getD r []).getD (p r) 0 = i.2.2

open Classical in
/-- THE HOUR-GLASS as a decision problem over bitstrings. -/
noncomputable def hourGlassDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HourGlassInstance) x with
  | some i => decide (WellFormed i ∧ HourGlassFeasible i)
  | none => false

/-- **THE HOUR-GLASS is NP-complete.** Source: Petersen (2015), Theorem 2, an unrefereed
preprint. -/
public theorem_wanted hourGlass_npComplete :
    hourGlassDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hourGlassDec

end MetaMathlibExt.Complexity.NPComplete.HourGlass
