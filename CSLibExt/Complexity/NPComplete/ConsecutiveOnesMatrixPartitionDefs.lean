/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSECUTIVE ONES MATRIX PARTITION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR15] CONSECUTIVE ONES MATRIX PARTITION
(attributed to W. Lipski, Jr. [1978], private communication).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixPartition

/-- An instance: the number of columns `n` and the rows of `A` (each a list of `n` entries,
`true` for `1`). -/
abbrev ConsecutiveOnesMatrixPartitionInstance := ℕ × List (List Bool)

/-- Well-formedness of an instance: every row has exactly `n` entries. -/
def WellFormed (i : ConsecutiveOnesMatrixPartitionInstance) : Prop :=
  ∀ row ∈ i.2, row.length = i.1

/-- The entry `a_rc` of `A` in row `r` and column `c` (indices from `0`). -/
def entry (i : ConsecutiveOnesMatrixPartitionInstance) (r : Fin i.2.length) (c : Fin i.1) :
    Bool :=
  (i.2.get r).getD c false

/-- The rows can be split into the group `g r = true` and the group `g r = false` so that the
matrix of each group has the consecutive ones property. -/
def ConsecutiveOnesMatrixPartitionFeasible (i : ConsecutiveOnesMatrixPartitionInstance) :
    Prop :=
  ∃ g : Fin i.2.length → Bool,
    ConsecutiveOnesMatrixAugmentation.HasConsecutiveOnes (fun r c => g r && entry i r c) ∧
      ConsecutiveOnesMatrixAugmentation.HasConsecutiveOnes (fun r c => !g r && entry i r c)

open Classical in
/-- CONSECUTIVE ONES MATRIX PARTITION as a decision problem over bitstrings. -/
noncomputable def consecutiveOnesMatrixPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsecutiveOnesMatrixPartitionInstance) x with
  | some i => decide (WellFormed i ∧ ConsecutiveOnesMatrixPartitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixPartition
