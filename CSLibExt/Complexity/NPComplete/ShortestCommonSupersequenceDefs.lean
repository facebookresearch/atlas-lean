/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSEQUENCE: definitions

Source:
K.-J. Räihä and E. Ukkonen, "The shortest common supersequence problem over binary alphabet is
NP-complete", Theoretical Computer Science 16 (1981), 187-198. (D. Maier, "The complexity of
some problems on subsequences and supersequences", JACM 25 (1978), 322-336, proves SCS only for
a five-symbol alphabet; the binary case is Räihä-Ukkonen.)
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequence

/-- **Shortest common supersequence instances.** An instance of SHORTEST COMMON SUPERSEQUENCE is a
pair $(R, K)$ of a list $R$ of binary strings (lists of booleans) and a natural number $K$, the
length bound. -/
abbrev ShortestCommonSupersequenceInstance := List (List Bool) × ℕ

/-- **Feasible shortest common supersequence instances.** An instance $(R, K)$ of SHORTEST COMMON
SUPERSEQUENCE, a list $R$ of lists of booleans together with a natural number $K$, is feasible
when there is a list $w$ of booleans of length at most $K$ such that every list in $R$ is a
subsequence of $w$ (its entries occur in $w$ in the same order, not necessarily consecutively). -/
def ShortestCommonSupersequenceFeasible
    (i : ShortestCommonSupersequenceInstance) : Prop :=
  ∃ super : List Bool, super.length ≤ i.2 ∧ ∀ s ∈ i.1, s.Sublist super

open Classical in
/-- **The SHORTEST COMMON SUPERSEQUENCE decision problem.** SHORTEST COMMON SUPERSEQUENCE is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding, to a pair $(R, K)$ of a list $R$ of lists of booleans and a natural number
$K$ for which some list of booleans of length at most $K$ has every list in $R$ as a subsequence.
Bitstrings that do not decode to such a pair are rejected. -/
noncomputable def shortestCommonSupersequenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestCommonSupersequenceInstance) x with
  | some i => decide (ShortestCommonSupersequenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequence
