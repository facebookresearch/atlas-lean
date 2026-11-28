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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SudokuDefs

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
