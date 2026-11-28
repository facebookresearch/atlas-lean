/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH WITH FORBIDDEN PAIRS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS;
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of
program test paths", IEEE Transactions on Software Engineering SE-2 (1976), 227-231,
doi:10.1109/TSE.1976.233819.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairs

/-- An instance: vertex count `m`, arc list, source `s`, target `t`, and the list of pairs
`C`. -/
abbrev PathWithForbiddenPairsInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × List (ℕ × ℕ)

/-- Well-formedness of an instance: the arcs, `s`, `t` and the pairs use vertices below `m`. -/
def WellFormed (i : PathWithForbiddenPairsInstance) : Prop :=
  (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧ i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧
    ∀ c ∈ i.2.2.2.2, c.1 < i.1 ∧ c.2 < i.1

/-- A directed path from `s` to `t` with at most one vertex from each pair of `C`. -/
def PathWithForbiddenPairsFeasible (i : PathWithForbiddenPairsInstance) : Prop :=
  ∃ p : List ℕ, p.head? = some i.2.2.1 ∧ p.getLast? = some i.2.2.2.1 ∧
    p.IsChain (fun u v => (u, v) ∈ i.2.1) ∧ p.Nodup ∧
      ∀ c ∈ i.2.2.2.2, c.1 ∈ p → c.2 ∈ p → c.1 = c.2

open Classical in
/-- PATH WITH FORBIDDEN PAIRS as a decision problem over bitstrings. -/
noncomputable def pathWithForbiddenPairsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathWithForbiddenPairsInstance) x with
  | some i => decide (WellFormed i ∧ PathWithForbiddenPairsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairs
