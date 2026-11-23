/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THIRD NORMAL FORM TEST is NP-complete

Source:
J. H. Jou and P. C. Fischer, "The complexity of recognizing 3NF relation schemes", Information
Processing Letters 14 (1982), 187-190, doi:10.1016/0020-0190(82)90034-5;
J. Demetrovics, G. Hencsey, L. Libkin and I. Muchnik, "Normal form relation schemes: a new
characterization", Acta Cybernetica 10 (1992), 141-153 ("recognizing 3NF is NP-complete in the
case of relation schemes", citing Jou and Fischer).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.FunctionalDependencies
public import WantedExt.Complexity.NPComplete.PrimeAttributeNameWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThirdNormalFormTest

open MetaMathlibExt.Complexity.NPComplete.PrimeAttributeName (deps)

/-!
# THIRD NORMAL FORM TEST is NP-complete

INSTANCE: a relation scheme: a set `U` of attribute names and a collection `F` of functional
dependencies on `U`.
QUESTION: is `⟨U, F⟩` in third normal form, i.e., for every nontrivial dependency `X → A` in
the closure `F⁺` of `F` (`X ⊆ U`, `A ∈ U - X`), is `X` a superkey or `A` a prime attribute (an
attribute belonging to some key)?

Jou and Fischer prove that recognizing third normal form relation schemes is NP-complete (the
problem of their title; Demetrovics, Hencsey, Libkin and Muchnik record it as "recognizing 3NF
is NP-complete in the case of relation schemes").

The attribute names are `0, …, n - 1`, the elements of `Fin n`; a dependency is a pair of lists
of names, read as the pair of their sets, by `PrimeAttributeName.deps`, whose docstring explains
why CSLibExt's `Cslib.Databases.Derives` (Armstrong's axioms) generates the closure `F⁺`. A
superkey is `Cslib.Databases.IsSuperkey` (`X → U` is derivable) and a key is
`Cslib.Databases.IsCandidateKey` (a superkey no proper subset of which is a superkey), as in
`PrimeAttributeNameWanted`.

Membership in NP, with the number `n` of attributes in binary: if `X → A` is a nontrivial
dependency of `F⁺` with `X` not a superkey and `A` not prime, then computing the closure of `X`
from `F` adds `A` through some `W → Z` in `F` with `W` inside the closure of `X` (so `W` is not a
superkey) and `A ∈ Z - W`. So `⟨U, F⟩` is in third normal form if and only if, for every
`W → Z` in `F` and every `A ∈ Z - W`, `W` is a superkey or `A` lies in some key. An attribute that
occurs on no right-hand side of `F` is derivable only from sets containing it, so it lies in
every superkey; hence a superkey is determined by its part `R` among the attributes occurring on
right-hand sides (at most the input size many), being `R` together with all other attributes.
Whether such a set is a superkey (its closure contains every right-hand-side attribute), and
whether it is a key (no attribute of `R` can be dropped; dropping any other attribute loses it
from the closure), is decided in polynomial time by attribute closures on the listed attributes.
So the parts `R` of keys containing the attributes `A` form a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of attribute names (`U = Fin n`) and the functional
dependencies `F` as pairs of lists of names. -/
abbrev ThirdNormalFormTestInstance := ℕ × List (List ℕ × List ℕ)

/-- Third normal form of the scheme `⟨Fin n, F⟩`: every nontrivial derivable dependency
`X → {a}` (`a ∉ X`) has `X` a superkey or `a` in some key. -/
def IsThirdNormalForm (n : ℕ) (F : Finset (Cslib.Databases.FD (Fin n))) : Prop :=
  ∀ (X : Finset (Fin n)) (a : Fin n), a ∉ X → Cslib.Databases.Derives F ⟨X, {a}⟩ →
    Cslib.Databases.IsSuperkey F X ∨ ∃ K, Cslib.Databases.IsCandidateKey F K ∧ a ∈ K

/-- Well-formedness of an instance: every dependency is a pair of subsets of `U`. -/
def WellFormed (i : ThirdNormalFormTestInstance) : Prop :=
  ∀ p ∈ i.2, (∀ a ∈ p.1, a < i.1) ∧ ∀ a ∈ p.2, a < i.1

/-- The scheme `⟨U, F⟩` is in third normal form. -/
def ThirdNormalFormTestFeasible (i : ThirdNormalFormTestInstance) : Prop :=
  IsThirdNormalForm i.1 (deps i.1 i.2)

open Classical in
/-- THIRD NORMAL FORM TEST as a decision problem over bitstrings. -/
noncomputable def thirdNormalFormTestDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThirdNormalFormTestInstance) x with
  | some i => decide (WellFormed i ∧ ThirdNormalFormTestFeasible i)
  | none => false

/-- **THIRD NORMAL FORM TEST is NP-complete.** Source: Jou and Fischer (1982). -/
public theorem_wanted thirdNormalFormTest_npComplete :
    thirdNormalFormTestDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L thirdNormalFormTestDec

end MetaMathlibExt.Complexity.NPComplete.ThirdNormalFormTest
