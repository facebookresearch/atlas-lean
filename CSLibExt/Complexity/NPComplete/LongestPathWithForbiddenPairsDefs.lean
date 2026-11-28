/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST PATH WITH FORBIDDEN PAIRS: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), entry LONGEST PATH WITH FORBIDDEN PAIRS in its graph theory section (decision version;
the entry gives the Garey-Johnson code GT54), related to
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS;
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of program
test paths", IEEE Transactions on Software Engineering SE-2(3) (1976), 227-231,
doi:10.1109/TSE.1976.233819;
Garey and Johnson (1979), [GT39] HAMILTONIAN PATH (the case with no pairs).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestPathWithForbiddenPairs

/-- An instance: vertex count `n`, edge list, the list of pairs `C`, and the bound `K`. -/
abbrev LongestPathWithForbiddenPairsInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list is a simple graph on `0, …, n - 1`, the
pairs use vertices below `n`, and `0 < K`. -/
def WellFormed (i : LongestPathWithForbiddenPairsInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ c ∈ i.2.2.1, c.1 < i.1 ∧ c.2 < i.1) ∧ 0 < i.2.2.2

/-- A simple path with at least `K` edges containing at most one vertex from each pair. -/
def LongestPathWithForbiddenPairsFeasible (i : LongestPathWithForbiddenPairsInstance) : Prop :=
  ∃ p : List ℕ, i.2.2.2 + 1 ≤ p.length ∧ p.Nodup ∧ (∀ v ∈ p, v < i.1) ∧
    p.IsChain (fun u v => (u, v) ∈ i.2.1 ∨ (v, u) ∈ i.2.1) ∧
      ∀ c ∈ i.2.2.1, c.1 ∈ p → c.2 ∈ p → c.1 = c.2

open Classical in
/-- LONGEST PATH WITH FORBIDDEN PAIRS as a decision problem over bitstrings. -/
noncomputable def longestPathWithForbiddenPairsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestPathWithForbiddenPairsInstance) x with
  | some i => decide (WellFormed i ∧ LongestPathWithForbiddenPairsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LongestPathWithForbiddenPairs
