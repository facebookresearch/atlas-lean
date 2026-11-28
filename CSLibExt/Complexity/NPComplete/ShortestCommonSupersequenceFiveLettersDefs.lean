/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSEQUENCE over a 5-letter alphabet: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR8] SHORTEST COMMON
SUPERSEQUENCE, p. 228, comment: "Remains NP-complete even if |Σ| = 5";
D. Maier, "The complexity of some problems on subsequences and supersequences", Journal of the
ACM 25 (1978), 322-336, doi:10.1145/322063.322075.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequenceFiveLetters

/-- An instance: the strings of `R` (lists of symbols from `{0, …, 4}`) and the bound `K`. -/
abbrev ShortestCommonSupersequenceFiveLettersInstance := List (List ℕ) × ℕ

/-- Well-formedness of an instance: every symbol of every string of `R` is in
`Σ = {0, …, 4}`, and `0 < K`. -/
def WellFormed (i : ShortestCommonSupersequenceFiveLettersInstance) : Prop :=
  (∀ x ∈ i.1, ∀ c ∈ x, c < 5) ∧ 0 < i.2

/-- Some string over `Σ = {0, …, 4}` of length at most `K` has every string of `R` as a
subsequence. -/
def ShortestCommonSupersequenceFiveLettersFeasible
    (i : ShortestCommonSupersequenceFiveLettersInstance) : Prop :=
  ∃ w : List ℕ, (∀ c ∈ w, c < 5) ∧ w.length ≤ i.2 ∧ ∀ x ∈ i.1, x.Sublist w

open Classical in
/-- SHORTEST COMMON SUPERSEQUENCE over a 5-letter alphabet as a decision problem over
bitstrings. -/
noncomputable def shortestCommonSupersequenceFiveLettersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestCommonSupersequenceFiveLettersInstance) x with
  | some i => decide (WellFormed i ∧ ShortestCommonSupersequenceFiveLettersFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequenceFiveLetters
