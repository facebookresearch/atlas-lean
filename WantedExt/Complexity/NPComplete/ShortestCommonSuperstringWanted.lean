/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSTRING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR9] SHORTEST COMMON SUPERSTRING;
J. Gallant, D. Maier and J. A. Storer, "On finding minimal length superstrings", Journal of
Computer and System Sciences 20 (1980), 50-58, doi:10.1016/0022-0000(80)90004-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring

/-!
# SHORTEST COMMON SUPERSTRING is NP-complete

INSTANCE: a finite alphabet `Σ`, a finite set `R` of strings from `Σ*`, and a positive integer
`K`. QUESTION: is there a string `w ∈ Σ*` with `|w| ≤ K` such that each string `x ∈ R` is a
substring of `w`, i.e., `w = w₀ x w₁` where each `wᵢ ∈ Σ*`?

The alphabet is `{0, …, k - 1}` for a given `k`, and strings are lists of symbols. "`x` is a
substring of `w`" is core Lean's `List.IsInfix` (`x <:+: w`), defined as
`∃ s t, s ++ x ++ t = w`, the source's `w = w₀ x w₁`. The set `R` is given as a list; a repeated
entry repeats a constraint and changes nothing.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the alphabet size `k` (symbols `0, …, k - 1`), the strings of `R`, and the bound
`K`. -/
abbrev ShortestCommonSuperstringInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every symbol of every string of `R` is in the alphabet, and
`0 < K`. -/
def WellFormed (i : ShortestCommonSuperstringInstance) : Prop :=
  (∀ x ∈ i.2.1, ∀ c ∈ x, c < i.1) ∧ 0 < i.2.2

/-- Some string over the alphabet, of length at most `K`, contains every string of `R` as a
substring. -/
def ShortestCommonSuperstringFeasible (i : ShortestCommonSuperstringInstance) : Prop :=
  ∃ w : List ℕ, (∀ c ∈ w, c < i.1) ∧ w.length ≤ i.2.2 ∧ ∀ x ∈ i.2.1, x <:+: w

open Classical in
/-- SHORTEST COMMON SUPERSTRING as a decision problem over bitstrings. -/
noncomputable def shortestCommonSuperstringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestCommonSuperstringInstance) x with
  | some i => decide (WellFormed i ∧ ShortestCommonSuperstringFeasible i)
  | none => false

/-- **SHORTEST COMMON SUPERSTRING is NP-complete.** Source: Garey and Johnson (1979), [SR9];
Gallant, Maier and Storer (1980). -/
public theorem_wanted shortestCommonSuperstring_npComplete :
    shortestCommonSuperstringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestCommonSuperstringDec

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring
