/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEAK PARTITION is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982),
182-195, doi:10.1016/0196-6774(82)90018-9, problem [9] WEAK PARTITION (reference: Shamir,
independently rediscovered by van Emde Boas and by Rubin; transformation from PARTITION);
A. Shamir, "On the cryptocomplexity of knapsack systems", Proc. 11th Annual ACM Symposium on
Theory of Computing (1979), 118-129, doi:10.1145/800135.804405;
P. van Emde Boas, "Another NP-complete partition problem and the complexity of computing short
vectors in a lattice", Report 81-04, Department of Mathematics, University of Amsterdam (1981).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Partition
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeakPartition

open MetaMathlibExt.Complexity.NPComplete.Partition (PartitionInstance)

/-!
# WEAK PARTITION is NP-complete

INSTANCE: a finite set `A` and a size `s(a) ∈ ℤ⁺` for each `a ∈ A`. QUESTION: are there
disjoint non-empty subsets `A₁, A₂ ⊂ A` such that `∑_{a ∈ A₁} s(a) = ∑_{a ∈ A₂} s(a)`?

The instance is the list of sizes, as in the proved PARTITION of
`CSLibExt.Computability.Complexity.Karp.Partition` (whose instance type is reused): the elements
of `A` are the positions `Fin |A|` of the list, so equal sizes at different positions are
different elements, and `A₁`, `A₂` are finite sets of positions. Two disjoint non-empty subsets
are automatically proper subsets of `A`. Sizes are encoded in binary; the problem is
NP-complete in the ordinary (weak) sense, being solvable in pseudo-polynomial time by dynamic
programming.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: every size is positive. -/
def WellFormed (i : PartitionInstance) : Prop :=
  ∀ a ∈ i, 0 < a

/-- Some two disjoint non-empty sets `A₁`, `A₂` of elements have the same total size. -/
def WeakPartitionFeasible (i : PartitionInstance) : Prop :=
  ∃ A₁ A₂ : Finset (Fin i.length), Disjoint A₁ A₂ ∧ A₁.Nonempty ∧ A₂.Nonempty ∧
    ∑ a ∈ A₁, i.get a = ∑ a ∈ A₂, i.get a

open Classical in
/-- WEAK PARTITION as a decision problem over bitstrings. -/
noncomputable def weakPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionInstance) x with
  | some i => decide (WellFormed i ∧ WeakPartitionFeasible i)
  | none => false

/-- **WEAK PARTITION is NP-complete.** Source: Johnson, NP-completeness column (1982), problem
[9]; Shamir (1979); van Emde Boas (1981). -/
public theorem_wanted weakPartition_npComplete :
    weakPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weakPartitionDec

end MetaMathlibExt.Complexity.NPComplete.WeakPartition
