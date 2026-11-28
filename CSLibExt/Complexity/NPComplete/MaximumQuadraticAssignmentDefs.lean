/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM QUADRATIC ASSIGNMENT: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MAXIMUM
QUADRATIC ASSIGNMENT;
E. M. Arkin, R. Hassin and M. Sviridenko, "Approximating the maximum quadratic assignment
problem", Information Processing Letters 77 (2001), 13-16,
doi:10.1016/S0020-0190(00)00151-4.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.QuadraticAssignmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumQuadraticAssignment

/-- An instance: the size `n`, the matrices `A` and `B` as lists of rows, and the bound `K`. -/
abbrev MaximumQuadraticAssignmentInstance :=
  QuadraticAssignment.QuadraticAssignmentInstance

/-- The entry in row `k` and column `l` of a matrix given as a list of rows. -/
def entry (M : List (List ℕ)) (k l : ℕ) : ℕ :=
  (M.getD k []).getD l 0

/-- The `n × n` matrix `M` is symmetric. -/
def IsSymmetric (n : ℕ) (M : List (List ℕ)) : Prop :=
  ∀ k < n, ∀ l < n, entry M k l = entry M l k

/-- Well-formedness of an instance: `A` and `B` are `n × n` matrices
(`QuadraticAssignment.WellFormed`), both are symmetric, and `K` is positive. -/
def WellFormed (i : MaximumQuadraticAssignmentInstance) : Prop :=
  QuadraticAssignment.WellFormed i ∧ IsSymmetric i.1 i.2.1 ∧ IsSymmetric i.1 i.2.2.1 ∧
    0 < i.2.2.2

/-- Some permutation `π` of `[0, ..., n - 1]` has `∑_{i ≠ j} a_{π(i),π(j)} b_{i,j} ≥ K`. -/
def MaximumQuadraticAssignmentFeasible (i : MaximumQuadraticAssignmentInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    i.2.2.2 ≤ ∑ a ∈ Finset.range i.1, ∑ b ∈ (Finset.range i.1).filter (· ≠ a),
      entry i.2.1 (perm.getD a 0) (perm.getD b 0) * entry i.2.2.1 a b

open Classical in
/-- MAXIMUM QUADRATIC ASSIGNMENT as a decision problem over bitstrings. -/
noncomputable def maximumQuadraticAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumQuadraticAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ MaximumQuadraticAssignmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumQuadraticAssignment
