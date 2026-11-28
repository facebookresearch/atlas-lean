/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM FIXED-LENGTH DISJOINT PATHS with fixed `K ≥ 4`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND42] MAXIMUM FIXED-LENGTH DISJOINT PATHS,
p. 218, comment ("Remains NP-complete for fixed K ≥ 4");
A. Itai, Y. Perl and Y. Shiloach, "The complexity of finding maximum disjoint paths with length
constraints", Networks 12(3) (1982), 277-286, doi:10.1002/net.3230120306.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPathsFixedK

open MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPaths

/-- An instance for a fixed length: vertex count `n` (vertices `0, …, n - 1`), edge list, `s`,
`t`, `J`. -/
abbrev FixedLengthInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The MAXIMUM FIXED-LENGTH DISJOINT PATHS instance given by `i` and the length `K`. -/
abbrev withLength (i : FixedLengthInstance) (K : ℕ) : MaximumFixedLengthDisjointPathsInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, K)

open Classical in
/-- MAXIMUM FIXED-LENGTH DISJOINT PATHS with the length fixed to `K`, as a decision problem over
bitstrings. -/
noncomputable def fixedLengthDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedLengthInstance) x with
  | some i => decide (WellFormed (withLength i K) ∧
      MaximumFixedLengthDisjointPathsFeasible (withLength i K))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPathsFixedK
