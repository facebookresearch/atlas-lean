/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LENGTH-BOUNDED DISJOINT PATHS with fixed `K ≥ 5`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND41] MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS, p. 217 (comment: "Remains NP-complete for all fixed `K ≥ 5`");
A. Itai, Y. Perl, and Y. Shiloach, "The complexity of finding maximum disjoint
paths with length constraints", Networks 12 (1982), 277-286,
doi:10.1002/net.3230120306.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsFixedK

open MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPaths

/-- An instance for a fixed bound: vertex count `n` (vertices `0, ..., n - 1`), edge list,
`s`, `t`, `J`. -/
abbrev FixedBoundInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The MAXIMUM LENGTH-BOUNDED DISJOINT PATHS instance given by `i` and the bound `K`. -/
abbrev withBound (i : FixedBoundInstance) (K : ℕ) : MaximumLengthBoundedDisjointPathsInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, K)

open Classical in
/-- MAXIMUM LENGTH-BOUNDED DISJOINT PATHS with the bound fixed to `K`, as a decision problem
over bitstrings. -/
noncomputable def fixedBoundDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedBoundInstance) x with
  | some i => decide (WellFormed (withBound i K) ∧
      MaximumLengthBoundedDisjointPathsFeasible (withBound i K))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsFixedK
