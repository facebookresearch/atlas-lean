/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSEQUENCE over a 5-letter alphabet is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR8] SHORTEST COMMON
SUPERSEQUENCE, p. 228, comment: "Remains NP-complete even if |Σ| = 5";
D. Maier, "The complexity of some problems on subsequences and supersequences", Journal of the
ACM 25 (1978), 322-336, doi:10.1145/322063.322075.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequenceFiveLetters

/-!
# SHORTEST COMMON SUPERSEQUENCE over a 5-letter alphabet is NP-complete

INSTANCE: a finite alphabet `Σ` with `|Σ| = 5`, a finite set `R` of strings from `Σ*`, and a
positive integer `K`. QUESTION: is there a string `w ∈ Σ*` with `|w| ≤ K` such that each string
`x ∈ R` is a subsequence of `w`, i.e., `w = w₀x₁w₁x₂w₂ ⋯ x_kw_k` where each `wᵢ ∈ Σ*` and
`x = x₁x₂ ⋯ x_k`?

The alphabet is `Σ = {0, 1, 2, 3, 4}` and strings are lists of symbols. "`x` is a subsequence of
`w`" is core Lean's `List.Sublist` (`x <+ w`: `x` is obtained from `w` by deleting elements).
The set `R` is given as a list; a repeated entry repeats a constraint and changes nothing.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SHORTEST COMMON SUPERSEQUENCE over a 5-letter alphabet is NP-complete.** Source: Garey and
Johnson (1979), [SR8], comment; Maier (1978). -/
public theorem_wanted shortestCommonSupersequenceFiveLetters_npComplete :
    shortestCommonSupersequenceFiveLettersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestCommonSupersequenceFiveLettersDec

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequenceFiveLetters
