/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B-BALANCED CUT: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry
MINIMUM B-BALANCED CUT;
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1 (1976), 237-267, doi:10.1016/0304-3975(76)90059-1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND17] MINIMUM CUT INTO BOUNDED SETS, comment;
T. N. Bui and C. Jones, "Finding good approximate vertex and edge partitions is NP-hard",
Information Processing Letters 42 (1992), 153-159, doi:10.1016/0020-0190(92)90140-Q.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BBalancedCut

/-- An instance: the vertex count `n`, the vertex weights, the edges `(u, v, c(e))`, the balance
`b = p / q` as `(p, q)`, and the bound `K`. -/
abbrev BBalancedCutInstance := ℕ × List ℕ × List (ℕ × ℕ × ℕ) × (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: one weight per vertex; every edge joins two different
vertices below `n`, with at most one edge per unordered pair; `0 < b ≤ 1/2`; and `0 < K`. -/
def WellFormed (i : BBalancedCutInstance) : Prop :=
  i.2.1.length = i.1 ∧ i.2.2.1.Nodup ∧
    (∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1) ∧
    (∀ e1 ∈ i.2.2.1, ∀ e2 ∈ i.2.2.1,
      (e1.1 = e2.1 ∧ e1.2.1 = e2.2.1 ∨ e1.1 = e2.2.1 ∧ e1.2.1 = e2.1) → e1 = e2) ∧
    0 < i.2.2.2.1.1 ∧ 2 * i.2.2.2.1.1 ≤ i.2.2.2.1.2 ∧ 0 < i.2.2.2.2

/-- The total weight `w(S)` of a set `S` of vertices. -/
def weight (i : BBalancedCutInstance) (S : Finset ℕ) : ℕ :=
  ∑ v ∈ S, i.2.1.getD v 0

/-- The weight of the cut `C`: the total cost of the edges with exactly one endpoint in `C`. -/
def cutCost (i : BBalancedCutInstance) (C : Finset ℕ) : ℕ :=
  ((i.2.2.1.filter fun e => decide (e.1 ∈ C) ≠ decide (e.2.1 ∈ C)).map fun e => e.2.2).sum

/-- There is a cut `C ⊆ V` with `min {w(C), w(V − C)} ≥ b · w(V)` and weight at most `K`. -/
def BBalancedCutFeasible (i : BBalancedCutInstance) : Prop :=
  ∃ C : Finset ℕ, (∀ v ∈ C, v < i.1) ∧
    i.2.2.2.1.1 * weight i (Finset.range i.1) ≤
      i.2.2.2.1.2 * min (weight i C) (weight i (Finset.range i.1 \ C)) ∧
    cutCost i C ≤ i.2.2.2.2

open Classical in
/-- B-BALANCED CUT as a decision problem over bitstrings. -/
noncomputable def bBalancedCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BBalancedCutInstance) x with
  | some i => decide (WellFormed i ∧ BBalancedCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BBalancedCut
