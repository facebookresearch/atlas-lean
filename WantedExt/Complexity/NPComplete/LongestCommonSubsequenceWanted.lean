/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST COMMON SUBSEQUENCE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LONGEST COMMON
SUBSEQUENCE; D. Maier, "The complexity of some problems on subsequences and supersequences"
(1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestCommonSubsequence

/-!
# LONGEST COMMON SUBSEQUENCE is NP-complete

A list of binary strings (lists of Booleans) and a bound `K`. The question is whether the
strings have a common subsequence of length at least `K`. Two-string LCS is polynomial; the
number of strings is part of the input.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Longest-common-subsequence instances.** A longest-common-subsequence instance is a pair
$(R, K)$ of a finite list $R$ of binary strings (finite lists of booleans) and a natural number
$K$. -/
abbrev LongestCommonSubsequenceInstance := List (List Bool) × ℕ

/-- **Feasible longest-common-subsequence instances.** A longest-common-subsequence instance
$(R, K)$ is feasible when there is a binary string $w$ of length at least $K$ that is a
subsequence of every string in $R$, that is, $w$ is obtained from each string in $R$ by deleting
some of its entries. -/
def LongestCommonSubsequenceFeasible
    (i : LongestCommonSubsequenceInstance) : Prop :=
  ∃ common : List Bool, i.2 ≤ common.length ∧ ∀ s ∈ i.1, common.Sublist s

open Classical in
/-- **The LONGEST COMMON SUBSEQUENCE decision problem.** LONGEST COMMON SUBSEQUENCE is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding, to a feasible longest-common-subsequence instance. Bitstrings that do not
decode are rejected. -/
noncomputable def longestCommonSubsequenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestCommonSubsequenceInstance) x with
  | some i => decide (LongestCommonSubsequenceFeasible i)
  | none => false

/-- **LONGEST COMMON SUBSEQUENCE is NP-complete.** The LONGEST COMMON SUBSEQUENCE decision
problem, over binary strings, belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), LONGEST COMMON SUBSEQUENCE; D. Maier, "The
complexity of some problems on subsequences and supersequences" (1978). -/
public theorem_wanted longestCommonSubsequence_npComplete :
    longestCommonSubsequenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestCommonSubsequenceDec

end MetaMathlibExt.Complexity.NPComplete.LongestCommonSubsequence
