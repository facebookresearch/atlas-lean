/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSEST SUBSTRING is NP-complete

Source:
J. K. Lanctot, M. Li, B. Ma, S. Wang, and L. Zhang, "Distinguishing string selection
problems", Information and Computation 185 (2003), 41-55,
doi:10.1016/S0890-5401(03)00057-9;
M. Frances and A. Litman, "On covering problems of codes", Theory of Computing Systems 30
(1997), 113-119, doi:10.1007/BF02679443 (CLOSEST STRING, the special case `L = |sᵢ|`, is
NP-complete over the binary alphabet).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.InformationTheory.Hamming

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosestSubstring

/-!
# CLOSEST SUBSTRING is NP-complete

INSTANCE: an alphabet `Σ`, strings `s₁, ..., s_k` over `Σ` (of arbitrary lengths), a positive
integer `L ≤ min |sᵢ|`, and a nonnegative integer `d`. QUESTION: is there a string `t` of length
`L` over `Σ` such that every `sᵢ` has a substring (a block of consecutive letters) of length `L`
within Hamming distance `d` of `t`?

Representation. The alphabet is `Σ = {0, ..., a - 1}`, given by its size `a`; strings are lists
of letters. The candidate `t` is a word `Fin L → ℕ` with letters below `a`, the length-`L`
substring of `s` starting at position `j` (with `j + L ≤ |s|`) is the word
`k ↦ s[j + k]`, and the distance is Mathlib's `hammingDist`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **CLOSEST SUBSTRING is NP-complete.** Source: Lanctot, Li, Ma, Wang, and Zhang (2003);
Frances and Litman (1997). -/
public theorem_wanted closestSubstring_npComplete :
    closestSubstringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L closestSubstringDec

end MetaMathlibExt.Complexity.NPComplete.ClosestSubstring
