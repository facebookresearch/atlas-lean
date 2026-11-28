/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM COVER with sets of size at most 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 222, problem [SP5] MINIMUM COVER
(comment: remains NP-complete even if all `c ∈ C` have `|c| ≤ 3`);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SetCoverDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCoverSetSizeAtMostThree

/-- Well-formedness of an instance: it is a well-formed SET COVER instance (every set is a
duplicate-free list of elements of `S`), every set has at most three elements, and
`0 < K ≤ |C|`. -/
def WellFormed (i : SetCover.SetCoverInstance) : Prop :=
  SetCover.WellFormed i ∧ (∀ c ∈ i.2.1, c.length ≤ 3) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

open Classical in
/-- MINIMUM COVER with sets of size at most 3 as a decision problem over bitstrings. -/
noncomputable def minimumCoverSetSizeAtMostThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetCover.SetCoverInstance) x with
  | some i => decide (WellFormed i ∧ SetCover.SetCoverFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumCoverSetSizeAtMostThree
