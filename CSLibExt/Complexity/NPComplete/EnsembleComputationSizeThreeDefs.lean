/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENSEMBLE COMPUTATION with sets of size at most 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO9] ENSEMBLE COMPUTATION, comment
("Remains NP-complete even if each `c ∈ C` satisfies `|c| ≤ 3`. The analogous problem in which
`xᵢ` and `yᵢ` need not be disjoint for `1 ≤ i ≤ j` is also NP-complete under the same
restriction"); the entry's reference is "[Garey and Johnson, ——]. Transformation from VERTEX
COVER (see Section 3.2.2)", the book's Theorem 3.6.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EnsembleComputationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EnsembleComputationSizeThree

open MetaMathlibExt.Complexity.NPComplete.EnsembleComputation
  (EnsembleComputationInstance EnsembleComputationFeasible)

/-- Well-formedness of an instance: a well-formed ENSEMBLE COMPUTATION instance (every member of
`C` a strictly increasing list of elements of `A`, no member listed twice, `0 < J`) in which every
member of `C` has at most three elements. -/
def WellFormed (i : EnsembleComputationInstance) : Prop :=
  EnsembleComputation.WellFormed i ∧ ∀ c ∈ i.2.1, c.length ≤ 3

open Classical in
/-- ENSEMBLE COMPUTATION with sets of size at most 3 as a decision problem over bitstrings. -/
noncomputable def ensembleComputationSizeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EnsembleComputationInstance) x with
  | some i => decide (WellFormed i ∧ EnsembleComputationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EnsembleComputationSizeThree
