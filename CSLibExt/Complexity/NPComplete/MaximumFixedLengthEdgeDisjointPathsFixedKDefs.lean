/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM FIXED-LENGTH EDGE-DISJOINT PATHS with fixed `K ≥ 4`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND42] MAXIMUM FIXED-LENGTH DISJOINT PATHS,
p. 218, comment ("Corresponding problem for edge-disjoint paths is NP-complete for fixed
K ≥ 4");
A. Itai, Y. Perl and Y. Shiloach, "The complexity of finding maximum disjoint paths with length
constraints", Networks 12(3) (1982), 277-286, doi:10.1002/net.3230120306.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.MengerEdge
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthEdgeDisjointPathsFixedK

open MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPaths
open MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted

/-- An instance for a fixed length: vertex count `n` (vertices `0, …, n - 1`), edge list, `s`,
`t`, `J`. -/
abbrev FixedLengthInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The MAXIMUM FIXED-LENGTH DISJOINT PATHS instance given by `i` and the length `K`. -/
abbrev withLength (i : FixedLengthInstance) (K : ℕ) : MaximumFixedLengthDisjointPathsInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, K)

/-- There are `J` paths from `s` to `t` in `G`, pairwise sharing no edge, each with exactly `K`
edges. -/
def EdgeDisjointFeasible (i : MaximumFixedLengthDisjointPathsInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1)
    (paths : Fin i.2.2.2.2.1 → (Graph i).Path ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩),
    IsEdgeDisjointSTPaths paths ∧ ∀ j, (paths j).val.length = i.2.2.2.2.2

open Classical in
/-- MAXIMUM FIXED-LENGTH EDGE-DISJOINT PATHS with the length fixed to `K`, as a decision problem
over bitstrings. -/
noncomputable def fixedLengthDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedLengthInstance) x with
  | some i => decide (WellFormed (withLength i K) ∧ EdgeDisjointFeasible (withLength i K))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthEdgeDisjointPathsFixedK
