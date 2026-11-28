/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-DIMENSIONAL CONSECUTIVE SETS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR19] 2-DIMENSIONAL CONSECUTIVE
SETS;
W. Lipski, Jr., "One more polynomial complete consecutive retrieval problem", Information
Processing Letters 6 (1977), 91-93, doi:10.1016/0020-0190(77)90034-5.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSets

/-- An instance: the alphabet size `s` (symbols `0, ..., s - 1`) and the subsets `Σⱼ` (each a
list of symbols). -/
abbrev TwoDimensionalConsecutiveSetsInstance := ℕ × List (List ℕ)

/-- Well-formedness of an instance: every subset lists distinct symbols of the alphabet. -/
def WellFormed (i : TwoDimensionalConsecutiveSetsInstance) : Prop :=
  ∀ S ∈ i.2, S.Nodup ∧ ∀ x ∈ S, x < i.1

/-- Some assignment `g` of the symbols to the sets `X_{g(x)}` of a partition puts the elements
of each subset `Σⱼ` into distinct sets among `|Σⱼ|` consecutive ones `X_l, ..., X_{l+|Σⱼ|-1}`. -/
def TwoDimensionalConsecutiveSetsFeasible (i : TwoDimensionalConsecutiveSetsInstance) :
    Prop :=
  ∃ g : ℕ → ℕ, ∀ S ∈ i.2, (∀ x ∈ S, ∀ y ∈ S, g x = g y → x = y) ∧
    ∃ l : ℕ, ∀ x ∈ S, l ≤ g x ∧ g x < l + S.length

open Classical in
/-- 2-DIMENSIONAL CONSECUTIVE SETS as a decision problem over bitstrings. -/
noncomputable def twoDimensionalConsecutiveSetsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoDimensionalConsecutiveSetsInstance) x with
  | some i => decide (WellFormed i ∧ TwoDimensionalConsecutiveSetsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSets
