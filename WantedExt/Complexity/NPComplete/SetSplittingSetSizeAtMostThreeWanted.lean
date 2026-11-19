/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET SPLITTING with sets of size at most 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 221, problem [SP4] SET SPLITTING
(comment: remains NP-complete even if all `c ∈ C` have `|c| ≤ 3`);
L. Lovász, "Coverings and colorings of hypergraphs", in *Proceedings of the Fourth
Southeastern Conference on Combinatorics, Graph Theory, and Computing*, Utilitas Mathematica
(1973), 3-12.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SetSplittingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetSplittingSetSizeAtMostThree

/-!
# SET SPLITTING with sets of size at most 3 is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `S`, all `c ∈ C` with `|c| ≤ 3`.
QUESTION: is there a partition of `S` into two subsets `S₁` and `S₂` such that no subset in `C`
is entirely contained in either `S₁` or `S₂`?

This is the restriction of `WantedExt.Complexity.NPComplete.SetSplittingWanted` to sets of at
most three elements. The instance type, the parent well-formedness condition and the question
are that module's (`SetSplitting.SetSplittingInstance`, `SetSplitting.WellFormed`,
`SetSplitting.SetSplittingFeasible`): `S = {0, ..., n - 1}`, the sets are duplicate-free lists
of elements of `S`, and the question asks for a part `S₁ ⊆ S` (with `S₂ = S \ S₁`) that every
set meets and does not contain. `WellFormed` adds the restriction `|c| ≤ 3` (a duplicate-free
list has as many entries as elements).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed SET SPLITTING instance (every set is a
duplicate-free list of elements of `S`), and every set has at most three elements. -/
def WellFormed (i : SetSplitting.SetSplittingInstance) : Prop :=
  SetSplitting.WellFormed i ∧ ∀ c ∈ i.2, c.length ≤ 3

open Classical in
/-- SET SPLITTING with sets of size at most 3 as a decision problem over bitstrings. -/
noncomputable def setSplittingSetSizeAtMostThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetSplitting.SetSplittingInstance) x with
  | some i => decide (WellFormed i ∧ SetSplitting.SetSplittingFeasible i)
  | none => false

/-- **SET SPLITTING is NP-complete for sets of size at most 3.** Source: Garey and Johnson
(1979), [SP4]; Lovász (1973). -/
public theorem_wanted setSplittingSetSizeAtMostThree_npComplete :
    setSplittingSetSizeAtMostThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setSplittingSetSizeAtMostThreeDec

end MetaMathlibExt.Complexity.NPComplete.SetSplittingSetSizeAtMostThree
