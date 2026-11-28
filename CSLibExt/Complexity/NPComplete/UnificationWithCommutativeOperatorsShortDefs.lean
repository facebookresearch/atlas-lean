/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFICATION WITH COMMUTATIVE OPERATORS with short expressions: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN16] UNIFICATION
WITH COMMUTATIVE OPERATORS, p. 252, comment: "Remains NP-complete even if no `eᵢ` or `fᵢ`
contains more than 7 occurrences of constants and variables" (the entry credits the problem
to R. Sethi, private communication, 1977; the original was not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShort

open MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperators

/-- The number of occurrences of variables and constants in an expression given by its prefix
token list: the tokens `(0, v)` and `(1, c)`, i.e., those that are not the operator `(2, 0)`. -/
def leafCount (ts : List (ℕ × ℕ)) : ℕ :=
  ts.countP fun t => t.1 ≠ 2

/-- Well-formedness of an instance: it is a well-formed instance of UNIFICATION WITH
COMMUTATIVE OPERATORS, and no `eᵢ` or `fᵢ` contains more than 7 occurrences of constants and
variables. -/
def WellFormed (i : UnificationWithCommutativeOperatorsInstance) : Prop :=
  UnificationWithCommutativeOperators.WellFormed i ∧
    ∀ p ∈ i.2.2, leafCount p.1 ≤ 7 ∧ leafCount p.2 ≤ 7

open Classical in
/-- UNIFICATION WITH COMMUTATIVE OPERATORS with short expressions as a decision problem over
bitstrings. -/
noncomputable def unificationWithCommutativeOperatorsShortDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnificationWithCommutativeOperatorsInstance) x with
  | some i => decide (WellFormed i ∧ UnificationWithCommutativeOperatorsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShort
