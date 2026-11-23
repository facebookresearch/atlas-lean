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
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Databases.FunctionalDependencies
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

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

/-- An instance: the number of attributes `a` (attributes `0, ..., a - 1`), the functional
dependencies (pairs of attribute lists `(X, Y)` for `X → Y`), and the bound `M`. -/
abbrev MinimumCardinalityKeyInstance := ℕ × List (List ℕ × List ℕ) × ℕ

/-- The attribute set listed by `l`. -/
def attrs (n : ℕ) (l : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => (x : ℕ) ∈ l

/-- The functional dependencies of the instance as a finite set of `Cslib.Databases.FD`. -/
def deps (i : MinimumCardinalityKeyInstance) : Finset (Cslib.Databases.FD (Fin i.1)) :=
  (i.2.1.map fun f => (⟨attrs i.1 f.1, attrs i.1 f.2⟩ : Cslib.Databases.FD (Fin i.1))).toFinset

/-- Well-formedness of an instance: every dependency mentions only attributes of `A`, and `M`
is positive. -/
def WellFormed (i : MinimumCardinalityKeyInstance) : Prop :=
  (∀ f ∈ i.2.1, (∀ x ∈ f.1, x < i.1) ∧ ∀ x ∈ f.2, x < i.1) ∧ 0 < i.2.2

/-- Some set `K` of at most `M` attributes is a key: `K → A` is derivable from `F` with
Armstrong's axioms. -/
def MinimumCardinalityKeyFeasible (i : MinimumCardinalityKeyInstance) : Prop :=
  ∃ K : Finset (Fin i.1), K.card ≤ i.2.2 ∧ Cslib.Databases.IsSuperkey (deps i) K

open Classical in
/-- MINIMUM CARDINALITY KEY as a decision problem over bitstrings. -/
noncomputable def minimumCardinalityKeyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCardinalityKeyInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCardinalityKeyFeasible i)
  | none => false

/-- **MINIMUM CARDINALITY KEY is NP-complete.** Source: Garey and Johnson (1979), [SR26];
Lucchesi and Osborn (1978). -/
public theorem_wanted minimumCardinalityKey_npComplete :
    minimumCardinalityKeyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCardinalityKeyDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCardinalityKey
