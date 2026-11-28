/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFORM SPARSEST CUT: definitions

Source:
D. W. Matula and F. Shahrokhi, "Sparsest cuts and bottlenecks in graphs", Discrete Applied
Mathematics 27 (1990), 113-123, doi:10.1016/0166-218X(90)90133-W;
A. Gupta, K. Talwar and D. Witmer, "Sparsest cut on bounded treewidth graphs: algorithms and
hardness results", STOC 2013, doi:10.1145/2488608.2488644 (Section 1, recording the result).
-/
module

public import Mathlib.Data.Finset.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniformSparsestCut

/-- An instance: the number `n` of vertices, the edge list, and the bound `r` as a pair
`(num, den)` standing for `num / den`. -/
abbrev UniformSparsestCutInstance := ℕ × List (ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, ..., n - 1`,
and `r = num / den` has a positive denominator and is positive. -/
def WellFormed (i : UniformSparsestCutInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2.2 ∧ 0 < i.2.2.1

/-- The number of edges with exactly one end in `S`. -/
def cutSize (i : UniformSparsestCutInstance) (S : Finset ℕ) : ℕ :=
  (i.2.1.filter fun e => decide ((e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S))).length

/-- Some vertex set `S` with `0 < |S| < n` has sparsity
`cutSize S / (|S| · (n - |S|)) ≤ num / den`. -/
def UniformSparsestCutFeasible (i : UniformSparsestCutInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧ 0 < S.card ∧ S.card < i.1 ∧
    cutSize i S * i.2.2.2 ≤ i.2.2.1 * (S.card * (i.1 - S.card))

open Classical in
/-- UNIFORM SPARSEST CUT as a decision problem over bitstrings. -/
noncomputable def uniformSparsestCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniformSparsestCutInstance) x with
  | some i => decide (WellFormed i ∧ UniformSparsestCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UniformSparsestCut
