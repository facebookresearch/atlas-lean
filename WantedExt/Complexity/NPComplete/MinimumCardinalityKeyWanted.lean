/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CARDINALITY KEY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR26] MINIMUM
CARDINALITY KEY;
C. L. Lucchesi and S. L. Osborn, "Candidate keys for relations", Journal of
Computer and System Sciences 17 (1978), 270-279,
doi:10.1016/0022-0000(78)90009-0.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumCardinalityKeyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCardinalityKey

/-!
# MINIMUM CARDINALITY KEY is NP-complete

INSTANCE: a set `A` of attribute names, a collection `F` of functional dependencies (ordered
pairs of subsets of `A`), and a positive integer `M`. QUESTION: is there a key of cardinality
`M` or less for the relational system `⟨A, F⟩`, that is, a subset `K ⊆ A` with `|K| ≤ M` such
that `(K, A)` belongs to the closure `F*` of `F` under Armstrong's axioms?

The attributes are `A = {0, ..., a - 1}`, as `Fin a`. Each functional dependency is a pair of
attribute lists, read as the dependency `Cslib.Databases.FD` between the two attribute sets.
`(K, A) ∈ F*` is `Cslib.Databases.IsSuperkey F K` from `CSLibExt.Databases.FunctionalDependencies`:
the dependency `K → A` is derivable from `F` with Armstrong's axioms (`Cslib.Databases.Derives`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM CARDINALITY KEY is NP-complete.** Source: Garey and Johnson (1979), [SR26];
Lucchesi and Osborn (1978). -/
public theorem_wanted minimumCardinalityKey_npComplete :
    minimumCardinalityKeyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCardinalityKeyDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCardinalityKey
