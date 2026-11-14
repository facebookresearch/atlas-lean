/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ADDITIONAL KEY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR27] ADDITIONAL KEY, p. 232
(reference [Beeri and Bernstein, 1978]; transformation from HITTING SET), with the closure
`F*` as defined in [SR26] MINIMUM CARDINALITY KEY, p. 232;
C. Beeri and P. A. Bernstein, "Computational problems related to the design of normal form
relational schemas", ACM Transactions on Database Systems 4 (1979), 30-59,
doi:10.1145/320064.320066.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.FunctionalDependencies

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AdditionalKey

/-!
# ADDITIONAL KEY is NP-complete

INSTANCE: a set `A` of attribute names, a collection `F` of functional dependencies on `A`,
a subset `R ⊆ A`, and a set `K` of keys for the relational scheme `⟨R, F⟩`.
QUESTION: does `R` have a key not already contained in `K`, i.e., is there an `R' ⊆ R` such
that `R' ∉ K`, `(R', R) ∈ F*`, and for no `R'' ⊂ R'` is `(R'', R) ∈ F*`?

A functional dependency on `A` is an ordered pair of subsets of `A`. `(R', R) ∈ F*` is CSLibExt's
`Cslib.Databases.Derives F ⟨R', R⟩`, derivability by Armstrong's axioms (reflexivity,
augmentation, transitivity). Garey and Johnson define `F*` ([SR26]) as the least set with (1)
`F ⊆ F*`, (2) `B ⊆ C ⊆ A` implies `(C, B) ∈ F*`, (3) `(B, C), (C, D) ∈ F*` implies
`(B, D) ∈ F*`, and (4) `(B, C), (B, D) ∈ F*` implies `(B, C ∪ D) ∈ F*`; both rule sets are
sound and complete for implication of functional dependencies
(`Cslib.Databases.derives_iff_entails`), so they generate the same closure. A key for
`⟨R, F⟩` is a minimal subset `R' ⊆ R` with `(R', R) ∈ F*`: no proper subset `R'' ⊂ R'` has
`(R'', R) ∈ F*`. Garey and Johnson print the last clause with `⊆`; read literally,
`R'' = R'` would contradict `(R', R) ∈ F*`, so the clause means proper subsets, as the
definition of a key requires.

The attribute names are `0, …, n - 1`, the elements of `Fin n`; a dependency is a pair of
lists of names (`deps`), and `R` and each member of `K` are lists of names, all read as sets
(`attrs`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of attribute names (`A = Fin n`), the functional
dependencies `F` as pairs of lists of names, the subset `R`, and the known keys `K`. -/
abbrev AdditionalKeyInstance := ℕ × List (List ℕ × List ℕ) × List ℕ × List (List ℕ)

/-- The set of attribute names of `Fin n` listed in `l`. -/
def attrs (n : ℕ) (l : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun a => (a : ℕ) ∈ l

/-- The functional dependencies of the instance, as CSLibExt dependencies on `Fin n`. -/
def deps (n : ℕ) (F : List (List ℕ × List ℕ)) : Finset (Cslib.Databases.FD (Fin n)) :=
  (F.map fun p => (⟨attrs n p.1, attrs n p.2⟩ : Cslib.Databases.FD (Fin n))).toFinset

/-- `R'` is a key for the relational scheme `⟨R, F⟩`: a subset of `R` with `(R', R) ∈ F*`, no
proper subset of which has this property. -/
def IsKey {n : ℕ} (F : Finset (Cslib.Databases.FD (Fin n))) (R R' : Finset (Fin n)) : Prop :=
  R' ⊆ R ∧ Cslib.Databases.Derives F ⟨R', R⟩ ∧ ∀ R'' ⊂ R', ¬ Cslib.Databases.Derives F ⟨R'', R⟩

/-- Well-formedness of an instance: every dependency is a pair of subsets of `A`, `R ⊆ A`,
and every member of `K` is a subset of `A` that is a key for `⟨R, F⟩`. -/
def WellFormed (i : AdditionalKeyInstance) : Prop :=
  (∀ p ∈ i.2.1, (∀ a ∈ p.1, a < i.1) ∧ ∀ a ∈ p.2, a < i.1) ∧ (∀ a ∈ i.2.2.1, a < i.1) ∧
    ∀ k ∈ i.2.2.2, (∀ a ∈ k, a < i.1) ∧ IsKey (deps i.1 i.2.1) (attrs i.1 i.2.2.1) (attrs i.1 k)

/-- Some `R' ⊆ R` outside `K` has `(R', R) ∈ F*`, and no proper subset `R'' ⊂ R'` has
`(R'', R) ∈ F*`. -/
def AdditionalKeyFeasible (i : AdditionalKeyInstance) : Prop :=
  ∃ R' : Finset (Fin i.1), R' ⊆ attrs i.1 i.2.2.1 ∧ R' ∉ i.2.2.2.map (attrs i.1) ∧
    Cslib.Databases.Derives (deps i.1 i.2.1) ⟨R', attrs i.1 i.2.2.1⟩ ∧
    ∀ R'' ⊂ R', ¬ Cslib.Databases.Derives (deps i.1 i.2.1) ⟨R'', attrs i.1 i.2.2.1⟩

open Classical in
/-- ADDITIONAL KEY as a decision problem over bitstrings. -/
noncomputable def additionalKeyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AdditionalKeyInstance) x with
  | some i => decide (WellFormed i ∧ AdditionalKeyFeasible i)
  | none => false

/-- **ADDITIONAL KEY is NP-complete.** Source: Garey and Johnson (1979), [SR27]; Beeri and
Bernstein (1979). -/
public theorem_wanted additionalKey_npComplete :
    additionalKeyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L additionalKeyDec

end MetaMathlibExt.Complexity.NPComplete.AdditionalKey
