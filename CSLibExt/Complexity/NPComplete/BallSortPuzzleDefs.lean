/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BALL SORT PUZZLE: definitions

Source:
T. Ito, J. Kawahara, S. Minato, Y. Otachi, T. Saitoh, A. Suzuki, R. Uehara, T. Uno,
K. Yamanaka and R. Yoshinaka, "Sorting balls and water: equivalence and computational
complexity", Theoretical Computer Science 978 (2023), 114158, doi:10.1016/j.tcs.2023.114158,
Theorem 9 (BSP); arXiv:2202.09495.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BallSortPuzzle

/-- An instance `(h, k, F)`: the capacity `h`, the number `k` of empty bins, and the full bins
`F`, each the list of its colors from bottom to top. -/
abbrev BallSortPuzzleInstance := ℕ × ℕ × List (List ℕ)

/-- The initial configuration: the full bins followed by `k` empty bins. -/
def initial (i : BallSortPuzzleInstance) : List (List ℕ) := i.2.2 ++ List.replicate i.2.1 []

/-- A ball move with capacity `h` from configuration `s` to `s'`: the top ball `c` of bin `b₁`
moves onto bin `b₂ ≠ b₁`, which is empty or has top color `c` and holds fewer than `h` balls. -/
def BallMove (h : ℕ) (s s' : List (List ℕ)) : Prop :=
  ∃ b₁ b₂ : Fin s.length, b₁ ≠ b₂ ∧ ∃ (c : ℕ) (rest : List ℕ), s[b₁] = rest ++ [c] ∧
    (s[b₂] = [] ∨ s[b₂].getLast? = some c) ∧ s[b₂].length + 1 ≤ h ∧
    s' = (s.set b₁ rest).set b₂ (s[b₂] ++ [c])

/-- A configuration is sorted: every bin is empty or holds `h` balls of one color. -/
def Sorted (h : ℕ) (s : List (List ℕ)) : Prop :=
  ∀ bin ∈ s, bin = [] ∨ ∃ c, bin = List.replicate h c

/-- Well-formedness: every given bin is full, with exactly `h` balls. -/
def WellFormed (i : BallSortPuzzleInstance) : Prop :=
  ∀ bin ∈ i.2.2, bin.length = i.1

/-- Some sequence of ball moves turns the initial configuration into a sorted one. -/
def BallSortPuzzleFeasible (i : BallSortPuzzleInstance) : Prop :=
  ∃ s, Relation.ReflTransGen (BallMove i.1) (initial i) s ∧ Sorted i.1 s

open Classical in
/-- BALL SORT PUZZLE as a decision problem over bitstrings. -/
noncomputable def ballSortPuzzleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BallSortPuzzleInstance) x with
  | some i => decide (WellFormed i ∧ BallSortPuzzleFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BallSortPuzzle
