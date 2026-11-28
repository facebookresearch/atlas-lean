/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH ADDRESS EXPRESSIONS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO7] CODE GENERATION WITH ADDRESS
EXPRESSIONS, pp. 273-274 (reference [Szymanski, 1978]; transformation from 3SAT);
T. G. Szymanski, "Assembling code for machines with span-dependent instructions",
Communications of the ACM 21 (1978), 300-308, doi:10.1145/359460.359474.
-/
module

public import Mathlib.Data.Set.Operations
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressions

/-- An instance `(g, B, C, M)`: the list `g` of address expressions `g(I₁), …, g(Iₙ)` (see the
module docstring), and natural numbers `B`, `C` and `M`. -/
abbrev CodeGenerationWithAddressExpressionsInstance := List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ

/-- An expression of an instruction among `n` instructions: `Iⱼ` (`(0, j, 0)` with `j < n`),
`Iⱼ + k` (`(1, j, k)`) or `Iⱼ - k` (`(2, j, k)`) with `j < n` and `k ∈ Z⁺`, or `k`
(`(3, 0, k)`) with `k ∈ Z⁺`. -/
def IsAddressExpr (n : ℕ) (e : ℕ × ℕ × ℕ) : Prop :=
  (e.1 = 0 ∧ e.2.1 < n ∧ e.2.2 = 0) ∨ (e.1 = 1 ∧ e.2.1 < n ∧ 0 < e.2.2) ∨
    (e.1 = 2 ∧ e.2.1 < n ∧ 0 < e.2.2) ∨ (e.1 = 3 ∧ e.2.1 = 0 ∧ 0 < e.2.2)

/-- Well-formedness of an instance: every `g(Iᵢ)` is an expression of the form `Iⱼ`,
`Iⱼ + k`, `Iⱼ - k` or `k` with `Iⱼ ∈ I` and `k ∈ Z⁺`, and `B`, `C`, `M` are positive. -/
def WellFormed (i : CodeGenerationWithAddressExpressionsInstance) : Prop :=
  (∀ e ∈ i.1, IsAddressExpr i.1.length e) ∧ 0 < i.2.1 ∧ 0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- The value `h(Iᵢ)` of the expression `g(Iᵢ)` under the address assignment `f`: `f(Iⱼ)`,
`f(Iⱼ) + k`, `f(Iⱼ) - k` or `k` for `g(Iᵢ) = Iⱼ`, `Iⱼ + k`, `Iⱼ - k` or `k`. -/
def addressValue (g : List (ℕ × ℕ × ℕ)) (f : Fin g.length → ℕ) (x : Fin g.length) : ℤ :=
  let e := g[x]
  let fj : ℤ := if hj : e.2.1 < g.length then (f ⟨e.2.1, hj⟩ : ℤ) else 0
  if e.1 = 0 then fj else if e.1 = 1 then fj + e.2.2 else if e.1 = 2 then fj - e.2.2
  else e.2.2

/-- There is a one-to-one, order-preserving `f : I → {1, …, M}` under which every
instruction `Iᵢ` has `-C < f(Iᵢ) - h(Iᵢ) < B` (a one-byte instruction) or has `f(Iᵢ) + 1`
outside the range of `f` and at most `M` (room for a two-byte instruction within the `M`
bytes of memory). -/
def CodeGenerationWithAddressExpressionsFeasible
    (i : CodeGenerationWithAddressExpressionsInstance) : Prop :=
  ∃ f : Fin i.1.length → ℕ,
    (∀ x, 1 ≤ f x ∧ f x ≤ i.2.2.2) ∧ Function.Injective f ∧
      (∀ x y, x < y → f x < f y) ∧
      ∀ x, (-(i.2.2.1 : ℤ) < (f x : ℤ) - addressValue i.1 f x ∧
          (f x : ℤ) - addressValue i.1 f x < (i.2.1 : ℤ)) ∨
        (f x + 1 ≤ i.2.2.2 ∧ f x + 1 ∉ Set.range f)

open Classical in
/-- CODE GENERATION WITH ADDRESS EXPRESSIONS as a decision problem over bitstrings. -/
noncomputable def codeGenerationWithAddressExpressionsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CodeGenerationWithAddressExpressionsInstance) x with
  | some i => decide (WellFormed i ∧ CodeGenerationWithAddressExpressionsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressions
