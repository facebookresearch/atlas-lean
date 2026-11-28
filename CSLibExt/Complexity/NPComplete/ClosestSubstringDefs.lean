/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSEST SUBSTRING: definitions

Source:
J. K. Lanctot, M. Li, B. Ma, S. Wang, and L. Zhang, "Distinguishing string selection
problems", Information and Computation 185 (2003), 41-55,
doi:10.1016/S0890-5401(03)00057-9;
M. Frances and A. Litman, "On covering problems of codes", Theory of Computing Systems 30
(1997), 113-119, doi:10.1007/BF02679443 (CLOSEST STRING, the special case `L = |sᵢ|`, is
NP-complete over the binary alphabet).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.InformationTheory.Hamming

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosestSubstring

/-- An instance: the alphabet size `a`, the strings `s₁, ..., s_k`, the length `L`, and the
distance bound `d`. -/
abbrev ClosestSubstringInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: there is at least one string (so that `min |sᵢ|` exists),
every letter of every string is in the alphabet, `L` is positive, and `L ≤ |sᵢ|` for every
string. -/
def WellFormed (i : ClosestSubstringInstance) : Prop :=
  i.2.1 ≠ [] ∧ (∀ s ∈ i.2.1, ∀ x ∈ s, x < i.1) ∧ 0 < i.2.2.1 ∧ ∀ s ∈ i.2.1, i.2.2.1 ≤ s.length

/-- The length-`L` substring of `s` starting at position `j`, as a word `Fin L → ℕ`. -/
def substringAt (s : List ℕ) (j L : ℕ) : Fin L → ℕ := fun k => s.getD (j + k) 0

/-- A string `t` of length `L` over the alphabet such that every `sᵢ` has a length-`L`
substring within Hamming distance `d` of `t`. -/
def ClosestSubstringFeasible (i : ClosestSubstringInstance) : Prop :=
  ∃ t : Fin i.2.2.1 → ℕ, (∀ k, t k < i.1) ∧
    ∀ s ∈ i.2.1, ∃ j, j + i.2.2.1 ≤ s.length ∧
      hammingDist t (substringAt s j i.2.2.1) ≤ i.2.2.2

open Classical in
/-- CLOSEST SUBSTRING as a decision problem over bitstrings. -/
noncomputable def closestSubstringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ClosestSubstringInstance) x with
  | some i => decide (WellFormed i ∧ ClosestSubstringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ClosestSubstring
