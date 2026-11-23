/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET BASIS with sets of size at most 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 222, problem [SP7] SET BASIS
(comment: remains NP-complete if all `c ∈ C` have `|c| ≤ 3`);
L. J. Stockmeyer, "The set basis problem is NP-complete", Report RC-5431,
IBM Research Center, Yorktown Heights, NY (1975).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SetBasisWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetBasisSizeThree

open MetaMathlibExt.Complexity.NPComplete.SetBasis

/-!
# SET BASIS with sets of size at most 3 is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `S`, all `c ∈ C` with `|c| ≤ 3`, and a
positive integer `K ≤ |C|`.
QUESTION: is there a collection `B` of subsets of `S` with `|B| = K` such that, for each
`c ∈ C`, there is a subcollection of `B` whose union is exactly `c`?

This is the restriction of `WantedExt.Complexity.NPComplete.SetBasisWanted` ([SP7]) to sets of
at most three elements. The instance type, the parent well-formedness condition and the
question are that module's (`SetBasisInstance`, `SetBasis.WellFormed`, `SetBasisFeasible`):
`S` is `Fin m`, every member of `C` is a strictly increasing list of elements of `S`, no member
is listed twice, `0 < K ≤ |C|`, and the question asks for a `Finset` `B` of exactly `K` subsets
of `S` such that every member of `C` is `D.sup id` for some `D ⊆ B`. `WellFormed` adds the
restriction `|c| ≤ 3` (a strictly increasing list has as many entries as elements).

Garey and Johnson record the restriction in their comment on [SP7], whose reference is
Stockmeyer (1975); the comment adds that the problem is trivial when all `|c| ≤ 2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed SET BASIS instance (strictly
increasing lists of elements of `S`, no member listed twice, `0 < K ≤ |C|`) and every member of
`C` has at most three elements. -/
def WellFormed (i : SetBasisInstance) : Prop :=
  SetBasis.WellFormed i ∧ ∀ c ∈ i.2.1, c.length ≤ 3

open Classical in
/-- SET BASIS with sets of size at most 3 as a decision problem over bitstrings. -/
noncomputable def setBasisSizeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetBasisInstance) x with
  | some i => decide (WellFormed i ∧ SetBasisFeasible i)
  | none => false

/-- **SET BASIS with sets of size at most 3 is NP-complete.** Source: Garey and Johnson (1979),
[SP7]; Stockmeyer (1975). -/
public theorem_wanted setBasisSizeThree_npComplete :
    setBasisSizeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setBasisSizeThreeDec

end MetaMathlibExt.Complexity.NPComplete.SetBasisSizeThree
