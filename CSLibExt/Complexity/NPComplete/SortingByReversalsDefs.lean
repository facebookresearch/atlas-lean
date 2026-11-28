/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SORTING BY REVERSALS: definitions

Source:
A. Caprara, "Sorting permutations by reversals and Eulerian cycle decompositions", SIAM
Journal on Discrete Mathematics 12 (1999), 91-110, doi:10.1137/S089548019731994X;
problem as stated in P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization
problems*, entry MINIMUM SORTING BY REVERSALS.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SortingByReversals

/-- An instance: the permutation `π` as the list `[π(1), …, π(n)]`, and the bound `K`. -/
abbrev SortingByReversalsInstance := List ℕ × ℕ

/-- Reverse the entries of `l` in the (`0`-based) positions `i` through `j`. -/
def reversal (l : List ℕ) (i j : ℕ) : List ℕ :=
  l.take i ++ ((l.drop i).take (j + 1 - i)).reverse ++ l.drop (j + 1)

/-- Well-formedness of an instance: the list is a permutation of the numbers `1` to `n`, where
`n` is its length. -/
def WellFormed (i : SortingByReversalsInstance) : Prop :=
  i.1.Perm (List.range' 1 i.1.length)

/-- At most `K` reversals of intervals `[i, j]` (`i < j < n`), applied in order, turn `π` into
the identity `[1, 2, …, n]`. -/
def SortingByReversalsFeasible (i : SortingByReversalsInstance) : Prop :=
  ∃ ops : List (ℕ × ℕ), ops.length ≤ i.2 ∧ (∀ o ∈ ops, o.1 < o.2 ∧ o.2 < i.1.length) ∧
    ops.foldl (fun l o => reversal l o.1 o.2) i.1 = List.range' 1 i.1.length

open Classical in
/-- SORTING BY REVERSALS as a decision problem over bitstrings. -/
noncomputable def sortingByReversalsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SortingByReversalsInstance) x with
  | some i => decide (WellFormed i ∧ SortingByReversalsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SortingByReversals
