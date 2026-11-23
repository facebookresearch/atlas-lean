/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET PACKING with sets of size at most 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 221, problem [SP3] SET PACKING
(comment: remains NP-complete even if all `c ∈ C` have `|c| ≤ 3`);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SetPackingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetPackingSetSizeAtMostThree

/-!
# SET PACKING with sets of size at most 3 is NP-complete

INSTANCE: a collection `C` of finite sets, all `c ∈ C` with `|c| ≤ 3`, and a positive integer
`K ≤ |C|`. QUESTION: does `C` contain at least `K` mutually disjoint sets?

This is the restriction of `WantedExt.Complexity.NPComplete.SetPackingWanted` to sets of at
most three elements. The instance type, the parent well-formedness condition and the question
are that module's (`SetPacking.SetPackingInstance`, `SetPacking.WellFormed`,
`SetPacking.SetPackingFeasible`): the sets are duplicate-free lists over a universe
`{0, ..., n - 1}`, and the question asks for a duplicate-free sublist of at least `K` pairwise
disjoint sets. `WellFormed` adds the restriction `|c| ≤ 3` (a duplicate-free list has as many
entries as elements) and Garey and Johnson's bound `0 < K ≤ |C|`, with `|C|` the number of
listed sets.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed SET PACKING instance (every set is a
duplicate-free list of elements of the universe), every set has at most three elements, and
`0 < K ≤ |C|`. -/
def WellFormed (i : SetPacking.SetPackingInstance) : Prop :=
  SetPacking.WellFormed i ∧ (∀ c ∈ i.2.1, c.length ≤ 3) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

open Classical in
/-- SET PACKING with sets of size at most 3 as a decision problem over bitstrings. -/
noncomputable def setPackingSetSizeAtMostThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetPacking.SetPackingInstance) x with
  | some i => decide (WellFormed i ∧ SetPacking.SetPackingFeasible i)
  | none => false

/-- **SET PACKING is NP-complete for sets of size at most 3.** Source: Garey and Johnson (1979),
[SP3]; Karp (1972). -/
public theorem_wanted setPackingSetSizeAtMostThree_npComplete :
    setPackingSetSizeAtMostThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setPackingSetSizeAtMostThreeDec

end MetaMathlibExt.Complexity.NPComplete.SetPackingSetSizeAtMostThree
