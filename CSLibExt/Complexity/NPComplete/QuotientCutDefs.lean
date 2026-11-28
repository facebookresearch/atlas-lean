/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUOTIENT CUT: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MINIMUM QUOTIENT
CUT;
J. K. Park and C. A. Phillips, "Finding minimum-quotient cuts in planar graphs", Proceedings
of the 25th Annual ACM Symposium on Theory of Computing (STOC 1993), 766-775,
doi:10.1145/167088.167284.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BBalancedCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuotientCut

/-- An instance: the vertex count `n`, the vertex weights, the edges `(u, v, c(e))`, and the
bound `K`. -/
abbrev QuotientCutInstance := ℕ × List ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The same graph, weights, costs and bound as a `b`-balanced-cut instance, with `b = 1/2`. -/
def toBBalancedCut (i : QuotientCutInstance) : BBalancedCut.BBalancedCutInstance :=
  (i.1, i.2.1, i.2.2.1, (1, 2), i.2.2.2)

/-- Well-formedness of an instance (`BBalancedCut.WellFormed`): one weight per vertex; every
edge joins two different vertices below `n`, with at most one edge per unordered pair; and
`0 < K`. -/
def WellFormed (i : QuotientCutInstance) : Prop :=
  BBalancedCut.WellFormed (toBBalancedCut i)

/-- Some cut `C ⊆ V` has `min {w(C), w(V − C)} > 0` and quotient at most `K`. -/
def QuotientCutFeasible (i : QuotientCutInstance) : Prop :=
  ∃ C : Finset ℕ, (∀ v ∈ C, v < i.1) ∧
    0 < min (BBalancedCut.weight (toBBalancedCut i) C)
      (BBalancedCut.weight (toBBalancedCut i) (Finset.range i.1 \ C)) ∧
    BBalancedCut.cutCost (toBBalancedCut i) C ≤
      i.2.2.2 * min (BBalancedCut.weight (toBBalancedCut i) C)
        (BBalancedCut.weight (toBBalancedCut i) (Finset.range i.1 \ C))

open Classical in
/-- QUOTIENT CUT as a decision problem over bitstrings. -/
noncomputable def quotientCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuotientCutInstance) x with
  | some i => decide (WellFormed i ∧ QuotientCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.QuotientCut
