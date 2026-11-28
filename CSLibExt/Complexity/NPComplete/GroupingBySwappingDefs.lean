/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GROUPING BY SWAPPING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR21] GROUPING BY SWAPPING (attributed to
T. D. Howell, "Grouping by swapping is NP-complete", unpublished manuscript (1977)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GroupingBySwapping

/-- An instance: the alphabet size `s` (symbols `0, ..., s - 1`), the string `x`, and the bound
`K`. -/
abbrev GroupingBySwappingInstance := ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: `x` is a string over the alphabet, and `K` is positive. -/
def WellFormed (i : GroupingBySwappingInstance) : Prop :=
  (∀ a ∈ i.2.1, a < i.1) ∧ 0 < i.2.2

/-- One adjacent symbol interchange: `b` is `a` with two adjacent symbols interchanged. -/
def Swap (a b : List ℕ) : Prop :=
  ∃ (l₁ l₂ : List ℕ) (c d : ℕ), a = l₁ ++ c :: d :: l₂ ∧ b = l₁ ++ d :: c :: l₂

/-- All occurrences of each symbol of `y` form a single block: `y` has no subsequence
`a b a` with `a ≠ b`. -/
def IsGrouped (y : List ℕ) : Prop :=
  ∀ a b : ℕ, a ≠ b → ¬ [a, b, a].Sublist y

/-- A sequence of at most `K` adjacent interchanges converts `x` into a grouped string: a list
of strings from `x` to `y` with at most `K + 1` entries, each obtained from the previous one by
one `Swap`, where `y` is grouped. -/
def GroupingBySwappingFeasible (i : GroupingBySwappingInstance) : Prop :=
  ∃ (ws : List (List ℕ)) (y : List ℕ), ws.head? = some i.2.1 ∧ ws.getLast? = some y ∧
    ws.length ≤ i.2.2 + 1 ∧ ws.IsChain Swap ∧ IsGrouped y

open Classical in
/-- GROUPING BY SWAPPING as a decision problem over bitstrings. -/
noncomputable def groupingBySwappingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GroupingBySwappingInstance) x with
  | some i => decide (WellFormed i ∧ GroupingBySwappingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GroupingBySwapping
