/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

/-!
# GROUPING BY SWAPPING: definitions

INSTANCE: a finite alphabet `Σ`, a string `x ∈ Σ*`, and a positive integer `K`. QUESTION: is
there a sequence of `K` or fewer adjacent symbol interchanges that converts `x` into a string
`y` in which all occurrences of each symbol `a ∈ Σ` are in a single block, i.e. `y` has no
subsequences of the form `a b a` for `a, b ∈ Σ` and `a ≠ b`?

This is Garey and Johnson's [SR21] (p. 231), with reference [Howell, 1977] (an unpublished
manuscript, "Grouping by swapping is NP-complete", per their bibliography), transformation from
FEEDBACK EDGE SET; the original was not available. Membership in NP: a shortest sequence of
interchanges from `x` to a given rearrangement `y` has at most `|x| (|x| - 1) / 2` steps (the
number of inversions), so a shortest witnessing sequence is a polynomial certificate even when
`K` is large.

The alphabet is `Σ = {0, ..., s - 1}` and strings are lists of symbols. One interchange is
`Swap a b`: `b` is `a` with two adjacent symbols interchanged (the interchange operation of
`StringToStringCorrection.Step`). As in `StringToStringCorrection`, a sequence of at most `K`
interchanges is a list of strings `x = w₀, w₁, ..., w_j = y` with `j ≤ K` (so at most `K + 1`
strings) in which each consecutive pair is one `Swap` (`List.IsChain`); `j = 0` (no
interchange, `y = x`) is included. A subsequence is a `List.Sublist`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR21] GROUPING BY SWAPPING (attributed to
T. D. Howell, "Grouping by swapping is NP-complete", unpublished manuscript (1977)).
-/

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
