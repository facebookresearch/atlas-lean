/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOYCE-CODD NORMAL FORM VIOLATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR29] BOYCE-CODD NORMAL FORM
VIOLATION, p. 233 (references [Bernstein and Beeri, 1976], [Beeri and Bernstein, 1978];
transformation from HITTING SET);
C. Beeri and P. A. Bernstein, "Computational problems related to the design of normal form
relational schemas", ACM Transactions on Database Systems 4 (1979), 30-59,
doi:10.1145/320064.320066.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Databases.NormalForms
public import CSLibExt.Complexity.NPComplete.PrimeAttributeNameDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoyceCoddNormalFormViolation

open PrimeAttributeName (attrs deps)

/-- An instance: the number `n` of attribute names (`A = Fin n`), the functional dependencies
`F` as pairs of lists of names, and the names of `A'`. -/
abbrev BoyceCoddNormalFormViolationInstance := ℕ × List (List ℕ × List ℕ) × List ℕ

/-- Well-formedness of an instance: every dependency is a pair of subsets of `A`, and
`A' ⊆ A`. -/
def WellFormed (i : BoyceCoddNormalFormViolationInstance) : Prop :=
  (∀ p ∈ i.2.1, (∀ a ∈ p.1, a < i.1) ∧ ∀ a ∈ p.2, a < i.1) ∧ ∀ a ∈ i.2.2, a < i.1

/-- `A'` is not in Boyce-Codd normal form for `⟨A, F⟩`. -/
def BoyceCoddNormalFormViolationFeasible (i : BoyceCoddNormalFormViolationInstance) : Prop :=
  ¬ Cslib.Databases.IsBCNF (deps i.1 i.2.1) (attrs i.1 i.2.2)

open Classical in
/-- BOYCE-CODD NORMAL FORM VIOLATION as a decision problem over bitstrings. -/
noncomputable def boyceCoddNormalFormViolationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoyceCoddNormalFormViolationInstance) x with
  | some i => decide (WellFormed i ∧ BoyceCoddNormalFormViolationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoyceCoddNormalFormViolation
