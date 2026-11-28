/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SORTING BY TRANSPOSITIONS: definitions

Source:
L. Bulteau, G. Fertin and I. Rusu, "Sorting by transpositions is difficult", SIAM Journal on
Discrete Mathematics 26 (2012), 1148-1180, doi:10.1137/110851390, arXiv:1011.1157.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions

/-- An instance: the permutation `π` of `⟦0 ; n⟧` as the list `[π(0), …, π(n)]`, and the
bound `k`. -/
abbrev SortingByTranspositionsInstance := List ℕ × ℕ

/-- Exchange the factor of `l` in positions `i, …, j - 1` with the factor in positions
`j, …, k - 1`. -/
def transposition (l : List ℕ) (i j k : ℕ) : List ℕ :=
  l.take i ++ (l.drop j).take (k - j) ++ (l.drop i).take (j - i) ++ l.drop k

/-- Well-formedness of an instance: for `n + 1` the length of the list, `n` is positive and the
list is a permutation of `⟦0 ; n⟧` that fixes `0` and `n`. -/
def WellFormed (i : SortingByTranspositionsInstance) : Prop :=
  2 ≤ i.1.length ∧ i.1.Perm (List.range i.1.length) ∧ i.1.getD 0 0 = 0 ∧
    i.1.getD (i.1.length - 1) 0 = i.1.length - 1

/-- `d_t(π) ≤ k`: at most `k` transpositions `τ_{i,j,k}` (`0 < i < j < k ≤ n`), applied in
order, turn `π` into the identity `[0, 1, …, n]`. -/
def SortingByTranspositionsFeasible (i : SortingByTranspositionsInstance) : Prop :=
  ∃ ops : List (ℕ × ℕ × ℕ), ops.length ≤ i.2 ∧
    (∀ o ∈ ops, 0 < o.1 ∧ o.1 < o.2.1 ∧ o.2.1 < o.2.2 ∧ o.2.2 ≤ i.1.length - 1) ∧
    ops.foldl (fun l o => transposition l o.1 o.2.1 o.2.2) i.1 = List.range i.1.length

open Classical in
/-- SORTING BY TRANSPOSITIONS as a decision problem over bitstrings. -/
noncomputable def sortingByTranspositionsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SortingByTranspositionsInstance) x with
  | some i => decide (WellFormed i ∧ SortingByTranspositionsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions
