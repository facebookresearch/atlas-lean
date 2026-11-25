/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM TEST SET with tests of size at most 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 222, problem [SP6] MINIMUM TEST SET;
K. M. J. De Bontridder, B. V. Halldórsson, M. M. Halldórsson, C. A. J. Hurkens,
J. K. Lenstra, R. Ravi and L. Stougie, "Approximation algorithms for the test cover problem",
Mathematical Programming, Series B 98 (2003), 477-491, doi:10.1007/s10107-003-0414-6,
Section 4 (the test cover problem with at most two items per test, TCP2, is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumTestSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSetSizeTwo

open MetaMathlibExt.Complexity.NPComplete.MinimumTestSet

/-!
# MINIMUM TEST SET with tests of size at most 2 is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `S`, every `c ∈ C` with `|c| ≤ 2`, and a
positive integer `K ≤ |C|`.
QUESTION: is there a subcollection `C' ⊆ C` with `|C'| ≤ K` such that for each pair of
distinct elements `u, v ∈ S`, there is some set `c ∈ C'` that contains exactly one of `u` and
`v`?

This is the restriction of `WantedExt.Complexity.NPComplete.MinimumTestSetWanted` ([SP6]) to
tests of at most two elements. The instance type, the parent well-formedness condition and the
question are that module's (`MinimumTestSetInstance`, `MinimumTestSet.WellFormed`,
`MinimumTestSetFeasible`): `S = {0, ..., n - 1}`, every test is a duplicate-free list of
elements of `S`, and the question asks for a sublist of at most `K` tests distinguishing every
pair of distinct elements of `S`. `WellFormed` adds that every test is listed in increasing
order and no test is listed twice, so that the list entries are exactly the members of `C` and
the list length is `|C|`; the restriction `|c| ≤ 2`; and Garey and Johnson's bound
`0 < K ≤ |C|`.

Garey and Johnson's comment on [SP6] states that the problem remains NP-complete when all
`|c| ≤ 3` and is solvable in polynomial time when all `|c| ≤ 2`. De Bontridder et al. (2003)
show that the case `|c| ≤ 2` is NP-hard (Section 4, by a relation with packing paths of length
2 in a graph) and record that the polynomial-time claim of Garey and Johnson was withdrawn
because of their work. Membership in NP is inherited from [SP6].

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed MINIMUM TEST SET instance, every test is
listed in increasing order and has at most two elements, no test is listed twice, and
`0 < K ≤ |C|`. -/
def WellFormed (i : MinimumTestSetInstance) : Prop :=
  MinimumTestSet.WellFormed i ∧ (∀ c ∈ i.2.1, c.Pairwise (· < ·) ∧ c.length ≤ 2) ∧
    i.2.1.Nodup ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

open Classical in
/-- MINIMUM TEST SET with tests of size at most 2 as a decision problem over bitstrings. -/
noncomputable def minimumTestSetSizeTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumTestSetInstance) x with
  | some i => decide (WellFormed i ∧ MinimumTestSetFeasible i)
  | none => false

/-- **MINIMUM TEST SET with tests of size at most 2 is NP-complete.** Source: Garey and Johnson
(1979), [SP6]; De Bontridder, Halldórsson, Halldórsson, Hurkens, Lenstra, Ravi and Stougie
(2003). -/
public theorem_wanted minimumTestSetSizeTwo_npComplete :
    minimumTestSetSizeTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumTestSetSizeTwoDec

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSetSizeTwo
