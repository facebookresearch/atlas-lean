/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SOLITAIRE UNO: definitions

Source:
E. D. Demaine, M. L. Demaine, N. J. A. Harvey, R. Uehara, T. Uno and Y. Uno, "UNO is hard, even
for a single player", Theoretical Computer Science 521 (2014), 51-61,
doi:10.1016/j.tcs.2013.11.023, Theorem 3 (Uno-1); arXiv:1003.2851.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Batteries.Data.List.Basic
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SolitaireUno

/-- An instance `(c, b, C)`: the number of colors `c`, the number of numbers `b`, and the cards
`(color, number)` of the multiset `C`. -/
abbrev SolitaireUnoInstance := ℕ × ℕ × List (ℕ × ℕ)

/-- Well-formedness: every card has a color in `{1, …, c}` and a number in `{1, …, b}`. -/
def WellFormed (i : SolitaireUnoInstance) : Prop :=
  ∀ t ∈ i.2.2, 1 ≤ t.1 ∧ t.1 ≤ i.1 ∧ 1 ≤ t.2 ∧ t.2 ≤ i.2.1

/-- All the cards can be played: some ordering of the multiset of cards has each card matching
the one before it in color or in number. -/
def SolitaireUnoFeasible (i : SolitaireUnoInstance) : Prop :=
  ∃ s : List (ℕ × ℕ), s.Perm i.2.2 ∧ s.IsChain fun t t' => t'.1 = t.1 ∨ t'.2 = t.2

open Classical in
/-- SOLITAIRE UNO as a decision problem over bitstrings. -/
noncomputable def solitaireUnoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SolitaireUnoInstance) x with
  | some i => decide (WellFormed i ∧ SolitaireUnoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SolitaireUno
