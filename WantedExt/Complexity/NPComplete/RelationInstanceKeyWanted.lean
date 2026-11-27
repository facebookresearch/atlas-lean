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
public import CSLibExt.Databases.FunctionalDependencies
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

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

/-- An instance: the number `m` of attributes, the rows of the relation (each a list of values),
and the bound `K`. -/
abbrev RelationInstanceKeyInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every row has exactly `m` values. -/
def WellFormed (i : RelationInstanceKeyInstance) : Prop :=
  ∀ t ∈ i.2.1, t.length = i.1

/-- The tuple of a row: attribute `a` has value `t[a]`. -/
def tuple (i : RelationInstanceKeyInstance) (t : List ℕ) : Fin i.1 → ℕ :=
  fun a => t.getD a 0

/-- The relation `r`: the set of tuples of the rows. -/
def relation (i : RelationInstanceKeyInstance) : Set (Fin i.1 → ℕ) :=
  {u | ∃ t ∈ i.2.1, u = tuple i t}

/-- Some set `X` of at most `K` attributes is a key of `r`: the dependency `X → U` holds in `r`,
so no two distinct tuples of `r` agree on `X`. -/
def RelationInstanceKeyFeasible (i : RelationInstanceKeyInstance) : Prop :=
  ∃ X : Finset (Fin i.1), X.card ≤ i.2.2 ∧
    (Cslib.Databases.FD.mk X Finset.univ).HoldsIn (relation i)

open Classical in
/-- KEY OF A RELATION INSTANCE as a decision problem over bitstrings. -/
noncomputable def relationInstanceKeyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RelationInstanceKeyInstance) x with
  | some i => decide (WellFormed i ∧ RelationInstanceKeyFeasible i)
  | none => false

/-- **KEY OF A RELATION INSTANCE is NP-complete.** Source: Beeri, Dowd, Fagin and Statman
(1984). -/
public theorem_wanted relationInstanceKey_npComplete :
    relationInstanceKeyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L relationInstanceKeyDec

end MetaMathlibExt.Complexity.NPComplete.RelationInstanceKey
