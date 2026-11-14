/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION FOR PARALLEL ASSIGNMENTS with at most two operands is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO6] CODE GENERATION FOR
PARALLEL ASSIGNMENTS, comment ("Remains NP-complete even if each `Bᵢ` satisfies `|Bᵢ| ≤ 2`");
R. Sethi, "A note on implementing parallel assignment instructions", Information Processing
Letters 2 (1973), 91-95, doi:10.1016/0020-0190(73)90024-0.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CodeGenerationParallelAssignmentsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignmentsTwoOperands

open MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignments
  (CodeGenerationParallelAssignmentsInstance CodeGenerationParallelAssignmentsFeasible)

/-!
# CODE GENERATION FOR PARALLEL ASSIGNMENTS with at most two operands is NP-complete

INSTANCE: a set `V = {v₁, ..., vₙ}` of variables, a set `A = {A₁, ..., Aₙ}` of assignments,
each `Aᵢ` of the form "`vᵢ ← op(Bᵢ)`" for some subset `Bᵢ ⊆ V` with `|Bᵢ| ≤ 2`, and a positive
integer `K`. QUESTION: is there an ordering `v_π(1), ..., v_π(n)` of `V` such that there are at
most `K` values of `i`, `1 ≤ i ≤ n`, for which `v_π(i) ∈ B_π(j)` for some `j > i`?

This is CODE GENERATION FOR PARALLEL ASSIGNMENTS
(`WantedExt.Complexity.NPComplete.CodeGenerationParallelAssignmentsWanted`) restricted to
operand sets of at most two variables. The instance type
`CodeGenerationParallelAssignmentsInstance` and the question
`CodeGenerationParallelAssignmentsFeasible` are those of that module, used directly; `WellFormed`
is that module's well-formedness strengthened by the restriction.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **CODE GENERATION FOR PARALLEL ASSIGNMENTS with at most two operands is NP-complete.** Source: Garey and Johnson (1979), [PO6], comment; Sethi (1973). -/
public theorem_wanted codeGenerationParallelAssignmentsTwoOperands_npComplete :
    codeGenerationParallelAssignmentsTwoOperandsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationParallelAssignmentsTwoOperandsDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignmentsTwoOperands
