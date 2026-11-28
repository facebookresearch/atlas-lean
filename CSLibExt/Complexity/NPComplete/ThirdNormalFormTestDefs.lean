/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THIRD NORMAL FORM TEST: definitions

Source:
J. H. Jou and P. C. Fischer, "The complexity of recognizing 3NF relation schemes", Information
Processing Letters 14 (1982), 187-190, doi:10.1016/0020-0190(82)90034-5;
J. Demetrovics, G. Hencsey, L. Libkin and I. Muchnik, "Normal form relation schemes: a new
characterization", Acta Cybernetica 10 (1992), 141-153 ("recognizing 3NF is NP-complete in the
case of relation schemes", citing Jou and Fischer).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.FunctionalDependencies
public import CSLibExt.Complexity.NPComplete.PrimeAttributeNameDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThirdNormalFormTest

open MetaMathlibExt.Complexity.NPComplete.PrimeAttributeName (deps)

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

end MetaMathlibExt.Complexity.NPComplete.ThirdNormalFormTest
