/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED COMPONENT SUM with 0/1 entries is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP18] EXPECTED COMPONENT SUM,
pp. 224-225 (comment: "NP-complete even if all entries are 0's and 1's.").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ExpectedComponentSumWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSumZeroOne

open MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSum

/-!
# EXPECTED COMPONENT SUM with 0/1 entries is NP-complete

EXPECTED COMPONENT SUM ([SP18], `ExpectedComponentSumWanted`) restricted to vectors whose
entries are all `0` or `1`. INSTANCE: a collection `C` of `m`-dimensional vectors with entries
in `{0, 1}`, positive integers `K` and `B`. QUESTION: is there a partition of `C` into disjoint
sets `C₁, …, C_K` such that `∑_{i=1}^{K} max_{1 ≤ j ≤ m} (∑_{v ∈ C_i} v_j) ≥ B`?

The instance, the component sum and the question are those of `ExpectedComponentSumWanted`;
only the restriction is new, in `WellFormed`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the [SP18] well-formedness, and every vector entry is `0`
or `1`. -/
def WellFormed (i : ExpectedComponentSumInstance) : Prop :=
  ExpectedComponentSum.WellFormed i ∧ ∀ v ∈ i.2.1, ∀ x ∈ v, x ≤ 1

open Classical in
/-- EXPECTED COMPONENT SUM with 0/1 entries as a decision problem over bitstrings. -/
noncomputable def expectedComponentSumZeroOneDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExpectedComponentSumInstance) x with
  | some i => decide (WellFormed i ∧ ExpectedComponentSumFeasible i)
  | none => false

/-- **EXPECTED COMPONENT SUM with 0/1 entries is NP-complete.** Source: Garey and Johnson
(1979), [SP18], comment. -/
public theorem_wanted expectedComponentSumZeroOne_npComplete :
    expectedComponentSumZeroOneDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L expectedComponentSumZeroOneDec

end MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSumZeroOne
