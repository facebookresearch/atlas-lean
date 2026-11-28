/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET BASIS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP7] SET BASIS;
L. J. Stockmeyer, "The set basis problem is NP-complete", Report RC-5431,
IBM Research Center, Yorktown Heights, NY (1975).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SetBasisDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetBasis

/-!
# SET BASIS is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `S`, and a positive integer `K ≤ |C|`.
QUESTION: is there a collection `B` of subsets of `S` with `|B| = K` such that, for each
`c ∈ C`, there is a subcollection of `B` whose union is exactly `c`?

The elements of `S` are `Fin m`; each member of `C` is given as a strictly increasing list,
and no member is listed twice, so the list length is `|C|`. `B` is a `Finset` of subsets
(distinct sets) and the union of a subcollection `D ⊆ B` is `D.sup id`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SET BASIS is NP-complete.** Source: Garey and Johnson (1979), [SP7]; Stockmeyer (1975). -/
public theorem_wanted setBasis_npComplete :
    setBasisDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setBasisDec

end MetaMathlibExt.Complexity.NPComplete.SetBasis
