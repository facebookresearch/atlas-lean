/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RATIO-CUT: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MINIMUM RATIO-CUT;
D. W. Matula and F. Shahrokhi, "Sparsest cuts and bottlenecks in graphs", Discrete Applied
Mathematics 27 (1990), 113-123, doi:10.1016/0166-218X(90)90133-W;
A. Gupta, K. Talwar and D. Witmer, "Sparsest cut on bounded treewidth graphs: algorithms and
hardness results", STOC 2013, 281-290, doi:10.1145/2488608.2488644 (Section 1, recording the
result).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RatioCut

/-- An instance: the vertex count `n`, the edges `(u, v, c(e))`, the commodities
`(s_i, t_i, d_i)`, and the bound `K`. -/
abbrev RatioCutInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every edge joins two different vertices below `n`, with at
most one edge per unordered pair; every commodity joins two different vertices below `n`; and
`0 < K`. -/
def WellFormed (i : RatioCutInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1) ∧
    (∀ e1 ∈ i.2.1, ∀ e2 ∈ i.2.1,
      (e1.1 = e2.1 ∧ e1.2.1 = e2.2.1 ∨ e1.1 = e2.2.1 ∧ e1.2.1 = e2.1) → e1 = e2) ∧
    (∀ q ∈ i.2.2.1, q.1 < i.1 ∧ q.2.1 < i.1 ∧ q.1 ≠ q.2.1) ∧ 0 < i.2.2.2

/-- The capacity of the cut `(V₁, V − V₁)`: the total capacity of the edges with exactly one
endpoint in `V₁`. -/
def capacity (i : RatioCutInstance) (V₁ : Finset ℕ) : ℕ :=
  ((i.2.1.filter fun e => decide (e.1 ∈ V₁) ≠ decide (e.2.1 ∈ V₁)).map fun e => e.2.2).sum

/-- The demand across the cut `(V₁, V − V₁)`: the total demand of the commodities with exactly
one of `s_i`, `t_i` in `V₁`. -/
def demand (i : RatioCutInstance) (V₁ : Finset ℕ) : ℕ :=
  ((i.2.2.1.filter fun q => decide (q.1 ∈ V₁) ≠ decide (q.2.1 ∈ V₁)).map fun q => q.2.2).sum

/-- Some cut `(V₁, V − V₁)` has positive demand across it and ratio at most `K`. -/
def RatioCutFeasible (i : RatioCutInstance) : Prop :=
  ∃ V₁ : Finset ℕ, (∀ v ∈ V₁, v < i.1) ∧ 0 < demand i V₁ ∧
    capacity i V₁ ≤ i.2.2.2 * demand i V₁

open Classical in
/-- RATIO-CUT as a decision problem over bitstrings. -/
noncomputable def ratioCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RatioCutInstance) x with
  | some i => decide (WellFormed i ∧ RatioCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RatioCut
