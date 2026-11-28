/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KEY OF A RELATION INSTANCE: definitions

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

public import CSLibExt.Databases.FunctionalDependencies
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RelationInstanceKey

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

end MetaMathlibExt.Complexity.NPComplete.RelationInstanceKey
