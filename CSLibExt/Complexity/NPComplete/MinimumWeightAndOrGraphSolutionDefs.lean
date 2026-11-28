/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM WEIGHT AND/OR GRAPH SOLUTION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS16] MINIMUM WEIGHT
AND/OR GRAPH SOLUTION;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolution

/-- An instance: the vertex count `n`, the vertex `s`, the arcs `(tail, head, weight)`, the
labels `f` (`true` for and), and the bound `K`. -/
abbrev MinimumWeightAndOrGraphSolutionInstance :=
  ℕ × ℕ × List (ℕ × ℕ × ℕ) × List Bool × ℕ

/-- Well-formedness of an instance: `s < n`; arcs join vertices below `n`, have positive
weights, and have distinct `(tail, head)` pairs; the graph is acyclic; `s` is the only vertex of
in-degree `0`; there is one label per vertex; and `0 < K`. -/
def WellFormed (i : MinimumWeightAndOrGraphSolutionInstance) : Prop :=
  i.2.1 < i.1 ∧
    (∀ a ∈ i.2.2.1, a.1 < i.1 ∧ a.2.1 < i.1 ∧ 0 < a.2.2) ∧
    (i.2.2.1.map fun a => (a.1, a.2.1)).Nodup ∧
    (∃ h : ℕ → ℕ, ∀ a ∈ i.2.2.1, h a.1 < h a.2.1) ∧
    (∀ v < i.1, (∀ a ∈ i.2.2.1, a.2.1 ≠ v) ↔ v = i.2.1) ∧
    i.2.2.2.1.length = i.1 ∧ 0 < i.2.2.2.2

/-- A solution subgraph of weight at most `K`: vertices `V'` and arc positions `A'` with
`s ∈ V'`, every arc of `A'` joining vertices of `V'`, all arcs leaving an and-vertex of `V'` in
`A'`, some arc leaving each or-vertex of `V'` of nonzero out-degree in `A'`, and total weight at
most `K`. -/
def MinimumWeightAndOrGraphSolutionFeasible
    (i : MinimumWeightAndOrGraphSolutionInstance) : Prop :=
  ∃ V' : Finset ℕ, ∃ A' : Finset ℕ, i.2.1 ∈ V' ∧ (∀ v ∈ V', v < i.1) ∧
    (∀ k ∈ A', ∃ h : k < i.2.2.1.length, i.2.2.1[k].1 ∈ V' ∧ i.2.2.1[k].2.1 ∈ V') ∧
    (∀ v ∈ V', i.2.2.2.1.getD v false = true →
      ∀ (k : ℕ) (h : k < i.2.2.1.length), i.2.2.1[k].1 = v → k ∈ A') ∧
    (∀ v ∈ V', i.2.2.2.1.getD v false = false →
      (∃ a ∈ i.2.2.1, a.1 = v) → ∃ k ∈ A', ∃ h : k < i.2.2.1.length, i.2.2.1[k].1 = v) ∧
    ∑ k ∈ A', (i.2.2.1.getD k (0, 0, 0)).2.2 ≤ i.2.2.2.2

open Classical in
/-- MINIMUM WEIGHT AND/OR GRAPH SOLUTION as a decision problem over bitstrings. -/
noncomputable def minimumWeightAndOrGraphSolutionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumWeightAndOrGraphSolutionInstance) x with
  | some i => decide (WellFormed i ∧ MinimumWeightAndOrGraphSolutionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolution
