/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION FOR PARALLEL ASSIGNMENTS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO6] CODE GENERATION
FOR PARALLEL ASSIGNMENTS;
R. Sethi, "A note on implementing parallel assignment instructions",
Information Processing Letters 2 (1973), 91-95,
doi:10.1016/0020-0190(73)90024-0.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignments

/-- An instance `(n, B, K)`: the number `n` of variables `v₀, …, v_{n-1}`, a 0-based list `B`
of operand sets as lists of variable indices (written `B₀, …, B_{n-1}` when there are `n`
assignments, with assignment `i` being `vᵢ ← op(Bᵢ)`), and the bound `K`. -/
abbrev CodeGenerationParallelAssignmentsInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: there are exactly `n` operand sets, each a list of
distinct variables in range (a subset of `V`), and `K` is positive. -/
def WellFormed (i : CodeGenerationParallelAssignmentsInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ b ∈ i.2.1, b.Nodup ∧ ∀ v ∈ b, v < i.1) ∧ 0 < i.2.2

/-- An ordering `π` of the variables with at most `K` positions `i` whose variable `v_π(i)`
lies in `B_π(j)` for some later position `j > i`. -/
def CodeGenerationParallelAssignmentsFeasible (i : CodeGenerationParallelAssignmentsInstance) :
    Prop :=
  ∃ π : Equiv.Perm (Fin i.1),
    {p : Fin i.1 | ∃ q, p < q ∧ ((π p : ℕ) ∈ i.2.1.getD (π q) [])}.ncard ≤ i.2.2

open Classical in
/-- CODE GENERATION FOR PARALLEL ASSIGNMENTS as a decision problem over bitstrings. -/
noncomputable def codeGenerationParallelAssignmentsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CodeGenerationParallelAssignmentsInstance) x with
  | some i => decide (WellFormed i ∧ CodeGenerationParallelAssignmentsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignments
