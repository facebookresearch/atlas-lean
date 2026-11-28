/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH ADDRESS EXPRESSIONS with B = 128 and C = 127: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO7] CODE GENERATION WITH ADDRESS
EXPRESSIONS, p. 274, comment: "Remains NP-complete for certain fixed values of B and C, e.g.,
128 and 127 (much smaller values also are possible)";
T. G. Szymanski, "Assembling code for machines with span-dependent instructions",
Communications of the ACM 21 (1978), 300-308, doi:10.1145/359460.359474.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressionsFixedBounds

open MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressions
  (CodeGenerationWithAddressExpressionsFeasible)

/-- An instance: the expressions `g(I₁), …, g(Iₙ)` (encoded as in [PO7]) and the memory bound
`M`. -/
abbrev CodeGenerationWithAddressExpressionsFixedBoundsInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- The [PO7] instance with `B = 128` and `C = 127`. -/
def withBounds (i : CodeGenerationWithAddressExpressionsFixedBoundsInstance) :
    CodeGenerationWithAddressExpressions.CodeGenerationWithAddressExpressionsInstance :=
  (i.1, 128, 127, i.2)

/-- Well-formedness of an instance: the [PO7] instance with `B = 128` and `C = 127` is well
formed (every `g(Iᵢ)` is an expression `Iⱼ`, `Iⱼ + k`, `Iⱼ - k` or `k` with `Iⱼ ∈ I` and
`k ∈ Z⁺`, and `M` is positive). -/
def WellFormed (i : CodeGenerationWithAddressExpressionsFixedBoundsInstance) : Prop :=
  CodeGenerationWithAddressExpressions.WellFormed (withBounds i)

/-- The [PO7] question with `B = 128` and `C = 127`. -/
def CodeGenerationWithAddressExpressionsFixedBoundsFeasible
    (i : CodeGenerationWithAddressExpressionsFixedBoundsInstance) : Prop :=
  CodeGenerationWithAddressExpressionsFeasible (withBounds i)

open Classical in
/-- CODE GENERATION WITH ADDRESS EXPRESSIONS with `B = 128` and `C = 127` as a decision problem
over bitstrings. -/
noncomputable def codeGenerationWithAddressExpressionsFixedBoundsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CodeGenerationWithAddressExpressionsFixedBoundsInstance) x with
  | some i => decide (WellFormed i ∧ CodeGenerationWithAddressExpressionsFixedBoundsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressionsFixedBounds
