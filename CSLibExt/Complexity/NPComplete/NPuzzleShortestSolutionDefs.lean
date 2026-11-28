/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# (n²−1)-PUZZLE SHORTEST SOLUTION: definitions

Source:
D. Ratner and M. Warmuth, "The (n²−1)-puzzle and related relocation problems",
Journal of Symbolic Computation 10(2) (1990), 111-137, doi:10.1016/S0747-7171(08)80001-6;
E. D. Demaine and M. Rudoy, "A simple proof that the (n²−1)-puzzle is hard",
Theoretical Computer Science 732 (2018), 80-84, doi:10.1016/j.tcs.2018.04.031 (Problem 1).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NPuzzleShortestSolution

/-- An instance: the board side `n`, the start configuration `s` and the target configuration
`t` (row by row, `0` for the hole), and the move bound `k`. -/
abbrev NPuzzleShortestSolutionInstance := ℕ × List (List ℕ) × List (List ℕ) × ℕ

/-- Well-formedness: `n ≥ 1`, both configurations have `n` rows of length `n`, and each lists
every label `0, …, n² − 1` exactly once. -/
def WellFormed (i : NPuzzleShortestSolutionInstance) : Prop :=
  1 ≤ i.1 ∧ i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    i.2.1.flatten.Perm (List.range (i.1 * i.1)) ∧ i.2.2.1.length = i.1 ∧
    (∀ row ∈ i.2.2.1, row.length = i.1) ∧ i.2.2.1.flatten.Perm (List.range (i.1 * i.1))

/-- The configuration given row by row, as a labelling of the cells `Fin n × Fin n`. -/
def config (n : ℕ) (rows : List (List ℕ)) : Fin n × Fin n → ℕ :=
  fun x => (rows.getD x.1 []).getD x.2 0

/-- One move takes configuration `a` to `b`: the hole, at cell `x`, exchanges cells with the
square at a cell `y` that shares a side with `x`. -/
def Move (n : ℕ) (a b : Fin n × Fin n → ℕ) : Prop :=
  ∃ x y : Fin n × Fin n, (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n).Adj x y ∧
    a x = 0 ∧ b = a ∘ Equiv.swap x y

/-- Some sequence of at most `k` moves converts `s` into `t`. -/
def NPuzzleShortestSolutionFeasible (i : NPuzzleShortestSolutionInstance) : Prop :=
  ∃ m ≤ i.2.2.2, ∃ f : ℕ → Fin i.1 × Fin i.1 → ℕ,
    f 0 = config i.1 i.2.1 ∧ f m = config i.1 i.2.2.1 ∧ ∀ j < m, Move i.1 (f j) (f (j + 1))

open Classical in
/-- (n²−1)-PUZZLE SHORTEST SOLUTION as a decision problem over bitstrings. -/
noncomputable def nPuzzleShortestSolutionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NPuzzleShortestSolutionInstance) x with
  | some i => decide (WellFormed i ∧ NPuzzleShortestSolutionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NPuzzleShortestSolution
