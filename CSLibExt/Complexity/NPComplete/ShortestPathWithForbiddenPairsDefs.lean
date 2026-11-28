/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST PATH WITH FORBIDDEN PAIRS: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), entry SHORTEST PATH WITH FORBIDDEN PAIRS in its graph theory section (decision
version);
V. Kann, "Polynomially bounded minimization problems that are hard to approximate", Nordic
Journal of Computing 1 (1994), 317-331 (conference version: ICALP 1993, LNCS 700, 52-63,
doi:10.1007/3-540-56939-1_61);
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of program
test paths", IEEE Transactions on Software Engineering SE-2(3) (1976), 227-231,
doi:10.1109/TSE.1976.233819;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestPathWithForbiddenPairs

/-- An instance: vertex count `n`, edge list, the list of pairs `C`, the initial vertex `s`, the
final vertex `f`, and the bound `K`. -/
abbrev ShortestPathWithForbiddenPairsInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- Well-formedness of an instance: the edge list is a simple graph on `0, …, n - 1`, the
pairs, `s` and `f` use vertices below `n`, and `0 < K`. -/
def WellFormed (i : ShortestPathWithForbiddenPairsInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ c ∈ i.2.2.1, c.1 < i.1 ∧ c.2 < i.1) ∧ i.2.2.2.1 < i.1 ∧ i.2.2.2.2.1 < i.1 ∧
      0 < i.2.2.2.2.2

/-- A simple path from `s` to `f` with at most `K` edges containing at most one vertex from
each pair. -/
def ShortestPathWithForbiddenPairsFeasible (i : ShortestPathWithForbiddenPairsInstance) :
    Prop :=
  ∃ p : List ℕ, p.head? = some i.2.2.2.1 ∧ p.getLast? = some i.2.2.2.2.1 ∧ p.Nodup ∧
    p.IsChain (fun u v => (u, v) ∈ i.2.1 ∨ (v, u) ∈ i.2.1) ∧
      (∀ c ∈ i.2.2.1, c.1 ∈ p → c.2 ∈ p → c.1 = c.2) ∧ p.length ≤ i.2.2.2.2.2 + 1

open Classical in
/-- SHORTEST PATH WITH FORBIDDEN PAIRS as a decision problem over bitstrings. -/
noncomputable def shortestPathWithForbiddenPairsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestPathWithForbiddenPairsInstance) x with
  | some i => decide (WellFormed i ∧ ShortestPathWithForbiddenPairsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShortestPathWithForbiddenPairs
