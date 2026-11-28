/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FARTHEST STRING: definitions

Source:
J. K. Lanctot, M. Li, B. Ma, S. Wang, and L. Zhang, "Distinguishing string
selection problems", Information and Computation 185 (2003), 41-55,
doi:10.1016/S0890-5401(03)00057-9 (preliminary version: Proc. 10th ACM-SIAM SODA
(1999)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DistinguishingStringSelectionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FarthestString

open DistinguishingStringSelection (DistinguishingStringSelectionInstance IsWord asWord
  DistinguishingStringSelectionFeasible)

/-- An instance: alphabet size `q` (symbols `0, ..., q - 1`), string length `L`, the strings
`s₁, ..., s_k`, and the distance bound `d`. -/
abbrev FarthestStringInstance := ℕ × ℕ × List (List ℕ) × ℕ

/-- The DISTINGUISHING STRING SELECTION instance with no bad strings, close threshold `0`, the
given strings as the good strings, and far threshold `d`. -/
def toDistinguishing (i : FarthestStringInstance) : DistinguishingStringSelectionInstance :=
  (i.1, i.2.1, [], i.2.2.1, 0, i.2.2.2)

/-- Well-formedness of an instance: every string has length `L` over the alphabet
`{0, ..., q - 1}` (the well-formedness of `toDistinguishing i`). -/
def WellFormed (i : FarthestStringInstance) : Prop :=
  DistinguishingStringSelection.WellFormed (toDistinguishing i)

/-- A string `t ∈ Σ^L` at Hamming distance at least `d` from every given string (the question of
`toDistinguishing i`). -/
def FarthestStringFeasible (i : FarthestStringInstance) : Prop :=
  DistinguishingStringSelectionFeasible (toDistinguishing i)

/-- The question unfolded: some word `t` of length `L` over `{0, ..., q - 1}` has Hamming
distance at least `d` from every given string. -/
theorem farthestStringFeasible_iff (i : FarthestStringInstance) :
    FarthestStringFeasible i ↔ ∃ t : List ℕ, IsWord i.1 i.2.1 t ∧
      ∀ s ∈ i.2.2.1, i.2.2.2 ≤ hammingDist (asWord i.2.1 t) (asWord i.2.1 s) := by
  constructor
  · rintro ⟨t, ht, -, h⟩
    exact ⟨t, ht, h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, by simp [toDistinguishing], h⟩

open Classical in
/-- FARTHEST STRING as a decision problem over bitstrings. -/
noncomputable def farthestStringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FarthestStringInstance) x with
  | some i => decide (WellFormed i ∧ FarthestStringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FarthestString
