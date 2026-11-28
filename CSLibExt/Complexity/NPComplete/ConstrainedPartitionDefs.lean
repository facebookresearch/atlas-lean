/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRAINED PARTITION: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM CONSTRAINED PARTITION;
D. Zuckerman, "On unapproximable versions of NP-complete problems", SIAM Journal on Computing
25 (1996), 1293-1304, doi:10.1137/S0097539794266407, Theorem 3.1, problem 20 (CONSTRAINED MAX
PARTITION); conference version: Proc. 8th Annual Structure in Complexity Theory Conference
(1993), 305-312, doi:10.1109/SCT.1993.336517;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SP12] PARTITION (the special case `a₀ ∈ S`,
`K = 1`).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Partition
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConstrainedPartition

open MetaMathlibExt.Complexity.NPComplete.Partition (PartitionInstance)

/-- An instance: the sizes (PARTITION's instance), the element `a₀`, the subset `S`, and the
bound `K`. -/
abbrev ConstrainedPartitionInstance := PartitionInstance × ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: every size is positive, `a₀` and the elements of `S` are
positions of `A`, and `K` is positive. -/
def WellFormed (i : ConstrainedPartitionInstance) : Prop :=
  (∀ a ∈ i.1, 0 < a) ∧ i.2.1 < i.1.length ∧ (∀ a ∈ i.2.2.1, a < i.1.length) ∧ 0 < i.2.2.2

/-- Some `A' ⊆ A` has the same total size as `A - A'`, and at least `K` elements of `S` lie on
the same side as `a₀`. -/
def ConstrainedPartitionFeasible (i : ConstrainedPartitionInstance) : Prop :=
  ∃ A' : Finset ℕ, A' ⊆ Finset.range i.1.length ∧
    ∑ a ∈ A', i.1.getD a 0 = ∑ a ∈ Finset.range i.1.length \ A', i.1.getD a 0 ∧
    i.2.2.2 ≤ (i.2.2.1.toFinset.filter fun a => (a ∈ A' ↔ i.2.1 ∈ A')).card

open Classical in
/-- CONSTRAINED PARTITION as a decision problem over bitstrings. -/
noncomputable def constrainedPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConstrainedPartitionInstance) x with
  | some i => decide (WellFormed i ∧ ConstrainedPartitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConstrainedPartition
