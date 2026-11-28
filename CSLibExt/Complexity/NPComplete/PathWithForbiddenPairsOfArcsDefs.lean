/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH WITH FORBIDDEN PAIRS OF ARCS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS,
p. 203 (comment: "Variant in which the "forbidden pairs" are arcs instead of vertices is also
NP-complete under the same restrictions.");
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of
program test paths", IEEE Transactions on Software Engineering SE-2 (1976), 227-231,
doi:10.1109/TSE.1976.233819.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairsOfArcs

/-- An instance: vertex count `m`, arc list, source `s`, target `t`, and the list `C` of pairs
of arcs. -/
abbrev PathWithForbiddenPairsOfArcsInstance :=
  ℕ × List (ℕ × ℕ) × ℕ × ℕ × List ((ℕ × ℕ) × (ℕ × ℕ))

/-- Well-formedness of an instance: the arcs, `s` and `t` use vertices below `m`, and both
members of every pair in `C` are arcs of `A`. -/
def WellFormed (i : PathWithForbiddenPairsOfArcsInstance) : Prop :=
  (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧ i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧
    ∀ c ∈ i.2.2.2.2, c.1 ∈ i.2.1 ∧ c.2 ∈ i.2.1

/-- A directed path from `s` to `t` containing at most one arc from each pair of `C`; the arcs
of the path `p` are the consecutive pairs `p.zip p.tail`. -/
def PathWithForbiddenPairsOfArcsFeasible (i : PathWithForbiddenPairsOfArcsInstance) : Prop :=
  ∃ p : List ℕ, p.head? = some i.2.2.1 ∧ p.getLast? = some i.2.2.2.1 ∧
    p.IsChain (fun u v => (u, v) ∈ i.2.1) ∧ p.Nodup ∧
      ∀ c ∈ i.2.2.2.2, c.1 ∈ p.zip p.tail → c.2 ∈ p.zip p.tail → c.1 = c.2

open Classical in
/-- PATH WITH FORBIDDEN PAIRS OF ARCS as a decision problem over bitstrings. -/
noncomputable def pathWithForbiddenPairsOfArcsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathWithForbiddenPairsOfArcsInstance) x with
  | some i => decide (WellFormed i ∧ PathWithForbiddenPairsOfArcsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairsOfArcs
