/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION FOR PARALLEL ASSIGNMENTS with at most two operands: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO6] CODE GENERATION FOR
PARALLEL ASSIGNMENTS, comment ("Remains NP-complete even if each `Bᵢ` satisfies `|Bᵢ| ≤ 2`");
R. Sethi, "A note on implementing parallel assignment instructions", Information Processing
Letters 2 (1973), 91-95, doi:10.1016/0020-0190(73)90024-0.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CodeGenerationParallelAssignmentsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignmentsTwoOperands

open MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignments
  (CodeGenerationParallelAssignmentsInstance CodeGenerationParallelAssignmentsFeasible)

/-- Well-formedness of an instance: a well-formed CODE GENERATION FOR PARALLEL ASSIGNMENTS
instance (exactly `n` operand sets, each a list of distinct variables in range, and `0 < K`) in
which every operand set has at most two elements. -/
def WellFormed (i : CodeGenerationParallelAssignmentsInstance) : Prop :=
  CodeGenerationParallelAssignments.WellFormed i ∧ ∀ b ∈ i.2.1, b.length ≤ 2

open Classical in
/-- CODE GENERATION FOR PARALLEL ASSIGNMENTS with at most two operands as a decision problem over bitstrings. -/
noncomputable def codeGenerationParallelAssignmentsTwoOperandsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CodeGenerationParallelAssignmentsInstance) x with
  | some i => decide (WellFormed i ∧ CodeGenerationParallelAssignmentsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignmentsTwoOperands
