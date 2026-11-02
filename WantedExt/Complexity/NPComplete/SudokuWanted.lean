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

/-- **Sudoku instances.** A Sudoku instance is a pair $(n, G)$ of a natural number $n$, the block
size, and a grid $G$ given as a finite list of rows, each row a finite list of natural numbers;
an entry $0$ stands for a blank cell. -/
abbrev SudokuInstance := ℕ × List (List ℕ)

/-- **Well-formed Sudoku instances.** A Sudoku instance $(n, G)$, with block size $n$ and grid $G$
a list of rows of natural numbers, is well formed when $n > 0$, $G$ has exactly $n^2$ rows, every
row of $G$ has exactly $n^2$ entries, and every entry of $G$ is at most $n^2$. -/
def WellFormed (i : SudokuInstance) : Prop :=
  0 < i.1 ∧ i.2.length = i.1 * i.1 ∧ (∀ row ∈ i.2, row.length = i.1 * i.1) ∧
    ∀ row ∈ i.2, ∀ x ∈ row, x ≤ i.1 * i.1

/-- **Feasible Sudoku instances.** A Sudoku instance $(n, G)$, with block size $n$ and grid $G$ a
list of rows of natural numbers, is feasible when there is a grid $C$ of natural numbers with
exactly $n^2$ rows, each of exactly $n^2$ entries, such that, indexing rows and columns from $0$:
for all $r, c < n^2$ the entry $G_{rc}$ is $0$ or equals $C_{rc}$, where an entry missing from
$G$ counts as $0$; every row of $C$ and every column of $C$ lists each of $1, \dots, n^2$ exactly
once; and for all $b, b' < n$ the $n^2$ entries $C_{bn + i,\, b'n + j}$ with $i, j < n$ list each
of $1, \dots, n^2$ exactly once. -/
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
/-- **SUDOKU as a decision problem.** The decision problem SUDOKU accepts a bitstring $x$ exactly
when $x$ decodes, under the canonical bitstring encoding of pairs of a natural number and a finite
list of finite lists of natural numbers, to a Sudoku instance that is well formed and feasible.
It rejects every bitstring that does not decode to an instance. -/
noncomputable def sudokuDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SudokuInstance) x with
  | some i => decide (WellFormed i ∧ SudokuFeasible i)
  | none => false

/-- **SUDOKU is NP-complete.** The decision problem SUDOKU lies in NP, and every decision problem
in NP has a polynomial-time many-one reduction to SUDOKU.

Source: T. Yato and T. Seta, "Complexity and completeness of
finding another solution and its application to puzzles" (2003). -/
public theorem_wanted sudoku_npComplete :
    sudokuDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sudokuDec

end MetaMathlibExt.Complexity.NPComplete.Sudoku
