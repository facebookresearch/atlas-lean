/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM COVER with sets of size at most 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 222, problem [SP5] MINIMUM COVER
(comment: remains NP-complete even if all `c ∈ C` have `|c| ≤ 3`);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SetCoverWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCoverSetSizeAtMostThree

/-!
# MINIMUM COVER with sets of size at most 3 is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `S`, all `c ∈ C` with `|c| ≤ 3`, and a
positive integer `K ≤ |C|`. QUESTION: does `C` contain a cover for `S` of size `K` or less,
i.e., a subset `C' ⊆ C` with `|C'| ≤ K` such that every element of `S` belongs to at least one
member of `C'`?

This is the restriction of `WantedExt.Complexity.NPComplete.SetCoverWanted` (Garey and
Johnson's MINIMUM COVER) to sets of at most three elements. The instance type, the parent
well-formedness condition and the question are that module's (`SetCover.SetCoverInstance`,
`SetCover.WellFormed`, `SetCover.SetCoverFeasible`): `S = {0, ..., n - 1}`, the sets are
duplicate-free lists of elements of `S`, and the question asks for a sublist of at most `K` sets
whose union is `S`. `WellFormed` adds the restriction `|c| ≤ 3` (a duplicate-free list has as
many entries as elements) and Garey and Johnson's bound `0 < K ≤ |C|`, with `|C|` the number
of listed sets.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MINIMUM COVER is NP-complete for sets of size at most 3.** Source: Garey and Johnson
(1979), [SP5]; Karp (1972). -/
public theorem_wanted minimumCoverSetSizeAtMostThree_npComplete :
    minimumCoverSetSizeAtMostThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCoverSetSizeAtMostThreeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCoverSetSizeAtMostThree
