/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KEY OF A RELATION INSTANCE is NP-complete

Source:
C. Beeri, M. Dowd, R. Fagin and R. Statman, "On the structure of Armstrong relations for
functional dependencies", Journal of the ACM 31 (1984), 30-46, doi:10.1145/2422.322414
(deciding whether a given relation has a key of cardinality below a given bound is
NP-complete), as recorded by J. Birnick, T. Bläsius, T. Friedrich, F. Naumann, T. Papenbrock and
M. Schirneck, "Hitting set enumeration with partial information for unique column combination
discovery", Proceedings of the VLDB Endowment 13 (2020), 2270-2283,
doi:10.14778/3407790.3407824. The schema-level problem, keys implied by functional
dependencies, is Garey and Johnson's [SR26] MINIMUM CARDINALITY KEY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RelationInstanceKeyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RelationInstanceKey

/-!
# KEY OF A RELATION INSTANCE is NP-complete

INSTANCE: a relation `r`, i.e., a finite set of tuples over a set `U` of attributes, and an
integer `K`.
QUESTION: is there a set `X ⊆ U` of at most `K` attributes on which no two distinct tuples of
`r` agree (a key of `r`)?

The attributes are `U = {0, …, m - 1}` and attribute values are natural numbers. The relation is
given as a list of rows, each a list of `m` values; a row is the tuple `Fin m → ℕ` (`tuple`), and
`r` is the set of these tuples (`relation`), so a row listed twice is one tuple. "No two
distinct tuples agree on `X`" is the functional dependency `X → U` holding in `r`, stated with
`Cslib.Databases.FD.HoldsIn` from `CSLibExt.Databases.FunctionalDependencies`: tuples of `r`
that agree on `X` agree everywhere, i.e., are equal. A set of attributes with this property is
a superkey of `r`; it contains a minimal one (a key in the strict sense) of no larger
cardinality, so asking for either gives the same question. The source's form ("a key of
cardinality less than a given value") is the same question with the bound shifted by one.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **KEY OF A RELATION INSTANCE is NP-complete.** Source: Beeri, Dowd, Fagin and Statman
(1984). -/
public theorem_wanted relationInstanceKey_npComplete :
    relationInstanceKeyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L relationInstanceKeyDec

end MetaMathlibExt.Complexity.NPComplete.RelationInstanceKey
