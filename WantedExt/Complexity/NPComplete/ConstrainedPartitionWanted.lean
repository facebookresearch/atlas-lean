/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRAINED PARTITION is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Partition
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConstrainedPartition

open MetaMathlibExt.Complexity.NPComplete.Partition (PartitionInstance)

/-!
# CONSTRAINED PARTITION is NP-complete

INSTANCE: a finite set `A`, a size `s(a) ∈ ℤ⁺` for each `a ∈ A`, an element `a₀ ∈ A`, a subset
`S ⊆ A`, and a positive integer `K`. QUESTION: is there a partition of `A`, i.e. a subset
`A' ⊆ A` with `∑_{a ∈ A'} s(a) = ∑_{a ∈ A - A'} s(a)`, such that at least `K` elements of `S`
are on the same side of the partition as `a₀`?

This is the decision version of MAXIMUM CONSTRAINED PARTITION in the compendium of Crescenzi
and Kann (Zuckerman's CONSTRAINED MAX PARTITION, whose measure is `|C ∩ T|` over equal
partitions `C` containing a given element `k`, with `T` the given subset). When `a₀ ∈ S` and
`K = 1` the side condition always holds, so these instances are PARTITION with positive sizes.

The sizes are a list, as in the proved PARTITION of
`CSLibExt.Computability.Complexity.Karp.Partition` (whose instance type is reused); the
elements of `A` are the positions `0, …, |A| - 1`. `a₀` is a position and `S` a list of
positions (a repeated position denotes the same element). `A'` is a set of positions; an
element `a` is on the same side as `a₀` when `a ∈ A' ↔ a₀ ∈ A'`. The sizes use the canonical
binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **CONSTRAINED PARTITION is NP-complete.** Source: Crescenzi and Kann, MAXIMUM CONSTRAINED
PARTITION; Zuckerman (1996), problem 20. The special case `a₀ ∈ S`, `K = 1` is PARTITION, Garey
and Johnson (1979), [SP12]. -/
public theorem_wanted constrainedPartition_npComplete :
    constrainedPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L constrainedPartitionDec

end MetaMathlibExt.Complexity.NPComplete.ConstrainedPartition
