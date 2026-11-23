/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION into halves of equal cardinality is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP12] PARTITION, comment ("Remains
NP-complete even if we require that `|A'| = |A|/2`, or if the elements in `A` are ordered as
`a₁, a₂, ..., a₂ₙ` and we require that `A'` contain exactly one of `a₂ᵢ₋₁, a₂ᵢ` for
`1 ≤ i ≤ n`"); the entry's reference is "[Karp, 1972]. Transformation from 3DM (see
Section 3.1.5)"; R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Partition
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EqualCardinalityPartition

open MetaMathlibExt.Complexity.NPComplete.Partition (PartitionInstance)

/-!
# PARTITION into halves of equal cardinality is NP-complete

INSTANCE: a finite set `A` and a size `s(a) ∈ ℤ⁺` for each `a ∈ A`. QUESTION: is there a
subset `A' ⊆ A` with `|A'| = |A|/2` such that `∑_{a ∈ A'} s(a) = ∑_{a ∈ A - A'} s(a)`?

The instance is the list of sizes, as in the proved PARTITION of
`CSLibExt.Computability.Complexity.Karp.Partition` (whose instance type is reused): the elements
of `A` are the positions of the list, and a subset `A'` is a sublist (a choice of positions).
`|A'| = |A|/2` is written `2 * |A'| = |A|`, which also requires `|A|` to be even; the two sums are
equal exactly when the sum over `A'` is half the total.

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

/-- Some sublist `A'` of half the length has half the total size. -/
def EqualCardinalityPartitionFeasible (i : PartitionInstance) : Prop :=
  ∃ s : List ℕ, s.Sublist i ∧ 2 * s.length = i.length ∧ s.sum * 2 = i.sum

open Classical in
/-- PARTITION into halves of equal cardinality as a decision problem over bitstrings. -/
noncomputable def equalCardinalityPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionInstance) x with
  | some i => decide (WellFormed i ∧ EqualCardinalityPartitionFeasible i)
  | none => false

/-- **PARTITION into halves of equal cardinality is NP-complete.** Source: Garey and Johnson (1979), [SP12], comment. -/
public theorem_wanted equalCardinalityPartition_npComplete :
    equalCardinalityPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L equalCardinalityPartitionDec

end MetaMathlibExt.Complexity.NPComplete.EqualCardinalityPartition
