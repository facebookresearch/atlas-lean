/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSTRING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR9] SHORTEST COMMON SUPERSTRING;
J. Gallant, D. Maier and J. A. Storer, "On finding minimal length superstrings", Journal of
Computer and System Sciences 20 (1980), 50-58, doi:10.1016/0022-0000(80)90004-5.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring

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

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring
