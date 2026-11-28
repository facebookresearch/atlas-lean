/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH UNFIXED VARIABLE LOCATIONS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO8] CODE GENERATION WITH UNFIXED
VARIABLE LOCATIONS (reference [Robertson, 1977]: E. L. Robertson, "Code generation for
short/long address machines", technical report, 1977; transformation from 3SAT);
journal version: E. L. Robertson, "Code generation and storage allocation for machines with
span-dependent instructions", ACM Transactions on Programming Languages and Systems 1 (1979),
71-83, doi:10.1145/357062.357067.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationUnfixedVariableLocations

/-!
# CODE GENERATION WITH UNFIXED VARIABLE LOCATIONS is NP-complete

INSTANCE: a sequence `I = (I₁, I₂, …, Iₙ)` of instructions, a finite set `V` of variables, an
assignment `g : I → I ∪ V`, and positive integers `B` and `M`.
QUESTION: can the instructions in `I` be stored as one- and two-byte instructions and the
variables stored among them so that the total memory required is at most `M`, i.e., is there a
one-to-one function `f : I ∪ V → {1, 2, …, M}` such that `f(Iᵢ) < f(Iⱼ)` whenever `i < j` and
such that, for `1 ≤ i ≤ n`, either `|f(Iᵢ) - f(g(Iᵢ))| < B` or `f(Iᵢ) + 1` is not in the range
of `f`?

The instructions are indexed by `Fin n`, `0`-based (index `j` is `I_{j+1}`), and the variables
by `Fin m`; `f` is a function on `Fin n ⊕ Fin m`. The instance lists `g(I₁), …, g(Iₙ)`, so
its length is `n`: `(0, j)` is the instruction `I_{j+1}` and `(1, j)` the variable `j`. As in
`CodeGenerationWithAddressExpressionsWanted` ([PO7]), the second byte of a two-byte instruction
must also lie in `{1, …, M}` (`f(Iᵢ) + 1 ≤ M`), so that the total memory required is at most
`M` as the question demands; the source's "i.e." condition leaves this implicit for the
instruction stored last.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance `(m, g, B, M)`: the number `m` of variables, the list `g` of instruction
targets `g(I₁), …, g(Iₙ)` (see the module docstring), and natural numbers `B` and `M`. -/
abbrev CodeGenerationUnfixedVariableLocationsInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: every `g(Iᵢ)` names an instruction `(0, j)` with `j < n`
or a variable `(1, j)` with `j < m`, and `B` and `M` are positive. -/
def WellFormed (i : CodeGenerationUnfixedVariableLocationsInstance) : Prop :=
  (∀ e ∈ i.2.1, (e.1 = 0 ∧ e.2 < i.2.1.length) ∨ (e.1 = 1 ∧ e.2 < i.1)) ∧
    0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- The location `f(g(Iᵢ))` of the target of instruction `x` under `f`. -/
def targetLocation (i : CodeGenerationUnfixedVariableLocationsInstance)
    (f : Fin i.2.1.length ⊕ Fin i.1 → ℕ) (x : Fin i.2.1.length) : ℕ :=
  let e := i.2.1[x]
  if e.1 = 0 then (if h : e.2 < i.2.1.length then f (Sum.inl ⟨e.2, h⟩) else 0)
  else if h : e.2 < i.1 then f (Sum.inr ⟨e.2, h⟩) else 0

/-- There is a one-to-one `f : I ∪ V → {1, …, M}`, increasing on the instructions, under which
every instruction `Iᵢ` has `|f(Iᵢ) - f(g(Iᵢ))| < B` (a one-byte instruction) or has
`f(Iᵢ) + 1` outside the range of `f` and at most `M` (room for a two-byte instruction within
the `M` bytes of memory). -/
def CodeGenerationUnfixedVariableLocationsFeasible
    (i : CodeGenerationUnfixedVariableLocationsInstance) : Prop :=
  ∃ f : Fin i.2.1.length ⊕ Fin i.1 → ℕ,
    (∀ x, 1 ≤ f x ∧ f x ≤ i.2.2.2) ∧ Function.Injective f ∧
      (∀ x y : Fin i.2.1.length, x < y → f (Sum.inl x) < f (Sum.inl y)) ∧
      ∀ x : Fin i.2.1.length,
        ((f (Sum.inl x) : ℤ) - targetLocation i f x).natAbs < i.2.2.1 ∨
          (f (Sum.inl x) + 1 ≤ i.2.2.2 ∧ f (Sum.inl x) + 1 ∉ Set.range f)

open Classical in
/-- CODE GENERATION WITH UNFIXED VARIABLE LOCATIONS as a decision problem over bitstrings. -/
noncomputable def codeGenerationUnfixedVariableLocationsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CodeGenerationUnfixedVariableLocationsInstance) x with
  | some i => decide (WellFormed i ∧ CodeGenerationUnfixedVariableLocationsFeasible i)
  | none => false

/-- **CODE GENERATION WITH UNFIXED VARIABLE LOCATIONS is NP-complete.** Source: Garey and
Johnson (1979), [PO8]; Robertson (1977, 1979). -/
public theorem_wanted codeGenerationUnfixedVariableLocations_npComplete :
    codeGenerationUnfixedVariableLocationsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationUnfixedVariableLocationsDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationUnfixedVariableLocations
