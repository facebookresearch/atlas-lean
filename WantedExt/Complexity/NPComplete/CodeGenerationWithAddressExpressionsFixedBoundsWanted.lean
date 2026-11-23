/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH ADDRESS EXPRESSIONS with B = 128 and C = 127 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO7] CODE GENERATION WITH ADDRESS
EXPRESSIONS, p. 274, comment: "Remains NP-complete for certain fixed values of B and C, e.g.,
128 and 127 (much smaller values also are possible)";
T. G. Szymanski, "Assembling code for machines with span-dependent instructions",
Communications of the ACM 21 (1978), 300-308, doi:10.1145/359460.359474.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CodeGenerationWithAddressExpressionsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressionsFixedBounds

open MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressions
  (CodeGenerationWithAddressExpressionsFeasible)

/-!
# CODE GENERATION WITH ADDRESS EXPRESSIONS with B = 128 and C = 127 is NP-complete

INSTANCE: a sequence `I = (I₁, I₂, …, Iₙ)` of instructions, for each `Iᵢ ∈ I` an expression
`g(Iᵢ)` of the form `Iⱼ`, `Iⱼ + k`, `Iⱼ - k`, or `k`, where `Iⱼ ∈ I` and `k ∈ Z⁺`, and a
positive integer `M`; the bounds are fixed at `B = 128` and `C = 127`.
QUESTION: is there a one-to-one function `f : I → {1, 2, …, M}` such that `f(Iᵢ) < f(Iⱼ)`
whenever `i < j` and such that, if `h(Iᵢ)` is `f(Iⱼ)`, `f(Iⱼ) ± k`, or `k` according to
`g(Iᵢ)`, then for each `i` either `-127 < f(Iᵢ) - h(Iᵢ) < 128` or `f(Iᵢ) + 1` is not in the
range of `f`?

This is [PO7] (`WantedExt.Complexity.NPComplete.CodeGenerationWithAddressExpressionsWanted`)
with `B` and `C` no longer part of the instance but fixed at the values the [PO7] comment
names, `B = 128` and `C = 127`. The expression encoding, its well-formedness and the question
(including the requirement that a two-byte instruction's second byte also lies in
`{1, …, M}`) are those of that module, applied to `(g, 128, 127, M)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding` (numbers in binary). Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **CODE GENERATION WITH ADDRESS EXPRESSIONS with `B = 128` and `C = 127` is NP-complete.**
Source: Garey and Johnson (1979), [PO7], comment; Szymanski (1978). -/
public theorem_wanted codeGenerationWithAddressExpressionsFixedBounds_npComplete :
    codeGenerationWithAddressExpressionsFixedBoundsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationWithAddressExpressionsFixedBoundsDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressionsFixedBounds
