/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSENSUS PATTERNS: definitions

Source:
M. Li, B. Ma and L. Wang, "Finding similar regions in many sequences", Journal of Computer and
System Sciences 65 (2002), 73-96, doi:10.1006/jcss.2002.1823 (Theorem 1: Consensus Patterns is
NP-hard over an alphabet of size four).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ClosestSubstringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsensusPatterns

open ClosestSubstring (ClosestSubstringInstance substringAt)

/-- Well-formedness of an instance: CLOSEST SUBSTRING's (at least one string, every letter in
the alphabet, `0 < L`, `L ≤ |sᵢ|` for every string), the strings are pairwise distinct, and all
strings have the same length. -/
def WellFormed (i : ClosestSubstringInstance) : Prop :=
  ClosestSubstring.WellFormed i ∧ i.2.1.Nodup ∧ ∀ s ∈ i.2.1, ∀ s' ∈ i.2.1, s.length = s'.length

/-- A median string `s` of length `L` over the alphabet and start positions `jᵢ` of
length-`L` substrings `tᵢ` of the strings `sᵢ` with `∑ᵢ d_H(s, tᵢ) ≤ D`. -/
def ConsensusPatternsFeasible (i : ClosestSubstringInstance) : Prop :=
  ∃ t : Fin i.2.2.1 → ℕ, (∀ k, t k < i.1) ∧
    ∃ js : List ℕ, js.length = i.2.1.length ∧ (∀ p ∈ i.2.1.zip js, p.2 + i.2.2.1 ≤ p.1.length) ∧
      ((i.2.1.zip js).map fun p => hammingDist t (substringAt p.1 p.2 i.2.2.1)).sum ≤ i.2.2.2

open Classical in
/-- CONSENSUS PATTERNS as a decision problem over bitstrings. -/
noncomputable def consensusPatternsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ClosestSubstringInstance) x with
  | some i => decide (WellFormed i ∧ ConsensusPatternsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConsensusPatterns
