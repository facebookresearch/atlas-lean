/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM COMMON STRING PARTITION: definitions

Source:
A. Goldstein, P. Kolman and J. Zheng, "Minimum common string partition problem: hardness and
approximations", Electronic Journal of Combinatorics 12 (2005), #R50, doi:10.37236/1947,
Theorem 2.2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCommonStringPartition

/-- An instance: the strings `A` and `B`, and the bound `K` on the number of blocks. -/
abbrev MinimumCommonStringPartitionInstance := List ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: `A` and `B` are related (permutations of each other). -/
def WellFormed (i : MinimumCommonStringPartitionInstance) : Prop :=
  i.1.Perm i.2.1

/-- Some common partition `⟨P, Q⟩` of `A` and `B` has at most `K` blocks: `P` concatenates
to `A`, `Q` concatenates to `B`, and `Q` is a permutation of `P`. -/
def MinimumCommonStringPartitionFeasible (i : MinimumCommonStringPartitionInstance) : Prop :=
  ∃ P Q : List (List ℕ), P.flatten = i.1 ∧ Q.flatten = i.2.1 ∧ Q.Perm P ∧ P.length ≤ i.2.2

open Classical in
/-- MINIMUM COMMON STRING PARTITION as a decision problem over bitstrings. -/
noncomputable def minimumCommonStringPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCommonStringPartitionInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCommonStringPartitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumCommonStringPartition
