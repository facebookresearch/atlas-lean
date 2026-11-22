/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUDOKU is NP-complete

Source:
T. Yato and T. Seta, "Complexity and completeness of finding another solution and its
application to puzzles" (2003).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Sudoku

/-!
# SUDOKU is NP-complete

A generalized Sudoku instance: block size `n` and an `n^2` by `n^2` grid with entries `0`
(blank) through `n^2`. The question is whether the grid can be completed so that every row,
column, and `n` by `n` block is a permutation of `1, …, n^2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A Sudoku instance: block size n, grid (0 blank). -/
abbrev SudokuInstance := ℕ × List (List ℕ)

/-- Well-formedness of an instance. -/
def WellFormed (i : SudokuInstance) : Prop :=
  0 < i.1 ∧ i.2.length = i.1 * i.1 ∧ (∀ row ∈ i.2, row.length = i.1 * i.1) ∧
    ∀ row ∈ i.2, ∀ x ∈ row, x ≤ i.1 * i.1

/-- A completion with every row, column, and block a permutation. -/
def SudokuFeasible
    (i : SudokuInstance) : Prop :=
  ∃ completion : List (List ℕ), completion.length = i.1 * i.1 ∧
    (∀ row ∈ completion, row.length = i.1 * i.1) ∧
    (∀ r < i.1 * i.1, ∀ c < i.1 * i.1, (i.2.getD r []).getD c 0 = 0 ∨
      (i.2.getD r []).getD c 0 = (completion.getD r []).getD c 0) ∧
    (∀ r < i.1 * i.1,
      (completion.getD r []).Perm ((List.range (i.1 * i.1)).map (· + 1))) ∧
    (∀ c < i.1 * i.1,
      ((List.range (i.1 * i.1)).map
        (fun r => (completion.getD r []).getD c 0)).Perm
        ((List.range (i.1 * i.1)).map (· + 1))) ∧
    ∀ br < i.1, ∀ bc < i.1,
      ((List.range (i.1 * i.1)).map (fun t =>
        (completion.getD (br * i.1 + t / i.1) []).getD (bc * i.1 + t % i.1) 0)).Perm
        ((List.range (i.1 * i.1)).map (· + 1))

open Classical in
/-- SUDOKU as a decision problem over bitstrings. -/
noncomputable def sudokuDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SudokuInstance) x with
  | some i => decide (WellFormed i ∧ SudokuFeasible i)
  | none => false

/-- **SUDOKU is NP-complete.** Source: T. Yato and T. Seta, "Complexity and completeness of
finding another solution and its application to puzzles" (2003). -/
public theorem_wanted sudoku_npComplete :
    sudokuDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sudokuDec

end MetaMathlibExt.Complexity.NPComplete.Sudoku
