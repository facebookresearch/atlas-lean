/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRIME ATTRIBUTE NAME: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR28] PRIME ATTRIBUTE NAME,
p. 232 (reference [Lucchesi and Osborn, 1977], printed "Osborne" there; transformation from
MINIMUM CARDINALITY KEY),
with the closure `F*` as defined in [SR26] MINIMUM CARDINALITY KEY, p. 232;
C. L. Lucchesi and S. L. Osborn, "Candidate keys for relations", Journal of Computer and
System Sciences 17 (1978), 270-279, doi:10.1016/0022-0000(78)90009-0.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.FunctionalDependencies

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrimeAttributeName

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

end MetaMathlibExt.Complexity.NPComplete.PrimeAttributeName
