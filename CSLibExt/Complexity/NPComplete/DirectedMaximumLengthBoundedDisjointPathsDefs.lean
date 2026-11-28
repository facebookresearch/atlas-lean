/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED MAXIMUM LENGTH-BOUNDED DISJOINT PATHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND41] MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS, p. 217, comment ("The same results hold if G is a directed
graph and the paths must be directed paths");
A. Itai, Y. Perl, and Y. Shiloach, "The complexity of finding maximum disjoint
paths with length constraints", Networks 12 (1982), 277-286,
doi:10.1002/net.3230120306.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedMaximumLengthBoundedDisjointPaths



open DirectedTwoDisjointConnectingPaths (IsDirectedPath)

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), arc list, `s`, `t`, `J`, `K`. -/
abbrev DirectedMaximumLengthBoundedDisjointPathsInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ

/-- Well-formedness of an instance: the arcs are distinct, loopless and between vertices, `s`
and `t` are distinct vertices, and `0 < J ≤ |V|` and `0 < K ≤ |V|`. -/
def WellFormed (i : DirectedMaximumLengthBoundedDisjointPathsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧
    0 < i.2.2.2.2.1 ∧ i.2.2.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2.2.2 ∧ i.2.2.2.2.2 ≤ i.1

/-- There are `J` different directed paths from `s` to `t` in `G`, pairwise sharing no vertex
other than `s` and `t`, each with at most `K` arcs. -/
def DirectedMaximumLengthBoundedDisjointPathsFeasible
    (i : DirectedMaximumLengthBoundedDisjointPathsInstance) : Prop :=
  ∃ paths : Fin i.2.2.2.2.1 → List ℕ, Function.Injective paths ∧
    (∀ j, IsDirectedPath i.2.1 i.2.2.1 i.2.2.2.1 (paths j) ∧
      (paths j).length ≤ i.2.2.2.2.2 + 1) ∧
    ∀ j j', j ≠ j' → ∀ v ∈ paths j, v ∈ paths j' → v = i.2.2.1 ∨ v = i.2.2.2.1

open Classical in
/-- DIRECTED MAXIMUM LENGTH-BOUNDED DISJOINT PATHS as a decision problem over bitstrings. -/
noncomputable def directedMaximumLengthBoundedDisjointPathsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedMaximumLengthBoundedDisjointPathsInstance) x with
  | some i => decide (WellFormed i ∧ DirectedMaximumLengthBoundedDisjointPathsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DirectedMaximumLengthBoundedDisjointPaths
