/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS with fixed `K ≥ 5`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 217, problem [ND41] MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS, comment: "Problem where paths need only be edge-disjoint is
NP-complete for all fixed `K ≥ 5`";
A. Itai, Y. Perl, and Y. Shiloach, "The complexity of finding maximum disjoint
paths with length constraints", Networks 12 (1982), 277-286,
doi:10.1002/net.3230120306.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.MengerEdge
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedEdgeDisjointPathsFixedK

open MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPaths
open MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted

/-- An instance for a fixed bound: vertex count `n` (vertices `0, ..., n - 1`), edge list,
`s`, `t`, `J`. -/
abbrev FixedBoundInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The MAXIMUM LENGTH-BOUNDED DISJOINT PATHS instance given by `i` and the bound `K`. -/
abbrev withBound (i : FixedBoundInstance) (K : ℕ) : MaximumLengthBoundedDisjointPathsInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, K)

/-- There are `J` paths from `s` to `t` in `G`, pairwise sharing no edge, each with at most `K`
edges. -/
def EdgeDisjointFeasible (i : MaximumLengthBoundedDisjointPathsInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1)
    (paths : Fin i.2.2.2.2.1 → (Graph i).Path ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩),
    IsEdgeDisjointSTPaths paths ∧ ∀ j, (paths j).val.length ≤ i.2.2.2.2.2

open Classical in
/-- MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS with the bound fixed to `K`, as a decision
problem over bitstrings. -/
noncomputable def fixedBoundDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedBoundInstance) x with
  | some i => decide (WellFormed (withBound i K) ∧ EdgeDisjointFeasible (withBound i K))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedEdgeDisjointPathsFixedK
