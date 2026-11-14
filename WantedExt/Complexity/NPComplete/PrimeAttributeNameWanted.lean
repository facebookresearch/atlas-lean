/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRIME ATTRIBUTE NAME is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR28] PRIME ATTRIBUTE NAME,
p. 232 (reference [Lucchesi and Osborne, 1977]; transformation from MINIMUM CARDINALITY KEY),
with the closure `F*` as defined in [SR26] MINIMUM CARDINALITY KEY, p. 232;
C. L. Lucchesi and S. L. Osborn, "Candidate keys for relations", Journal of Computer and
System Sciences 17 (1978), 270-279, doi:10.1016/0022-0000(78)90009-0.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.FunctionalDependencies

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrimeAttributeName

/-!
# PRIME ATTRIBUTE NAME is NP-complete

INSTANCE: a set `A` of attribute names, a collection `F` of functional dependencies on `A`,
and a specified name `x ∈ A`.
QUESTION: is `x` a "prime attribute name" for `⟨A, F⟩`, i.e., is there a key `K` for `⟨A, F⟩`
such that `x ∈ K`?

A functional dependency on `A` is an ordered pair of subsets of `A`. A key for `⟨A, F⟩` is a
minimal subset `K ⊆ A` such that the ordered pair `(K, A)` belongs to the closure `F*` of `F`
(Garey and Johnson, [SR26]): `Cslib.Databases.IsCandidateKey`, a superkey (`F` derives
`K → A`) no proper subset of which is a superkey. Derivability is CSLibExt's
`Cslib.Databases.Derives`, by Armstrong's axioms (reflexivity, augmentation, transitivity).
Garey and Johnson define `F*` as the least set with (1) `F ⊆ F*`, (2) `B ⊆ C ⊆ A` implies
`(C, B) ∈ F*`, (3) `(B, C), (C, D) ∈ F*` implies `(B, D) ∈ F*`, and (4)
`(B, C), (B, D) ∈ F*` implies `(B, C ∪ D) ∈ F*`; both rule sets are sound and complete for
implication of functional dependencies (`Cslib.Databases.derives_iff_entails`), so they
generate the same closure.

The attribute names are `0, …, n - 1`, the elements of `Fin n`; a dependency is a pair of
lists of names, read as the pair of their sets (`deps`).

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
dependencies `F` as pairs of lists of names, and the name `x`. -/
abbrev PrimeAttributeNameInstance := ℕ × List (List ℕ × List ℕ) × ℕ

/-- The set of attribute names of `Fin n` listed in `l`. -/
def attrs (n : ℕ) (l : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun a => (a : ℕ) ∈ l

/-- The functional dependencies of the instance, as CSLibExt dependencies on `Fin n`. -/
def deps (n : ℕ) (F : List (List ℕ × List ℕ)) : Finset (Cslib.Databases.FD (Fin n)) :=
  (F.map fun p => (⟨attrs n p.1, attrs n p.2⟩ : Cslib.Databases.FD (Fin n))).toFinset

/-- Well-formedness of an instance: every dependency is a pair of subsets of `A`, and
`x ∈ A`. -/
def WellFormed (i : PrimeAttributeNameInstance) : Prop :=
  (∀ p ∈ i.2.1, (∀ a ∈ p.1, a < i.1) ∧ ∀ a ∈ p.2, a < i.1) ∧ i.2.2 < i.1

/-- Some key for `⟨A, F⟩` contains `x`. -/
def PrimeAttributeNameFeasible (i : PrimeAttributeNameInstance) : Prop :=
  ∃ K : Finset (Fin i.1), Cslib.Databases.IsCandidateKey (deps i.1 i.2.1) K ∧
    ∃ a ∈ K, (a : ℕ) = i.2.2

open Classical in
/-- PRIME ATTRIBUTE NAME as a decision problem over bitstrings. -/
noncomputable def primeAttributeNameDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrimeAttributeNameInstance) x with
  | some i => decide (WellFormed i ∧ PrimeAttributeNameFeasible i)
  | none => false

/-- **PRIME ATTRIBUTE NAME is NP-complete.** Source: Garey and Johnson (1979), [SR28];
Lucchesi and Osborn (1978). -/
public theorem_wanted primeAttributeName_npComplete :
    primeAttributeNameDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L primeAttributeNameDec

end MetaMathlibExt.Complexity.NPComplete.PrimeAttributeName
