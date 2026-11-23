/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ŁUKASIEWICZ LOGIC SATISFIABILITY is NP-complete

Source:
D. Mundici, "Satisfiability in many-valued sentential logic is NP-complete", Theoretical
Computer Science 52 (1987), 145-153, doi:10.1016/0304-3975(87)90083-1;
Z. Haniková and F. Jankovec, "Satisfiability in Łukasiewicz logic and its unbounded relative",
CSL 2026, LIPIcs 363 (2026), 14:1-14:18, doi:10.4230/LIPIcs.CSL.2026.14, Section 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LukasiewiczSatisfiability

/-!
# ŁUKASIEWICZ LOGIC SATISFIABILITY is NP-complete

INSTANCE: a formula (term) `φ` of infinite-valued Łukasiewicz propositional logic over
variables `x₀, x₁, …`, built with the connectives `⊕`, `⊗`, `¬`, `→`, `∧`, `∨` and the
constants `0`, `1`. QUESTION: is `φ` satisfiable in the standard MV-algebra `[0, 1]Ł`, that is,
is there an assignment of real numbers in `[0, 1]` to the variables under which `φ` takes the
value `1`?

Mundici proves that satisfiability is NP-complete for the infinite-valued calculus of
Łukasiewicz (his abstract: "Cook's NP-completeness theorem is extended to all many-valued
sentential logics, including the infinite-valued calculus of Łukasiewicz"). The language and
semantics follow Haniková and Jankovec (Section 2), who use Mundici's result "on the
NP-completeness of the term satisfiability problem in `[0, 1]Ł`": the language of MV-algebras is
`⟨⊕, ⊗, ¬, →, 0, 1, ∧, ∨⟩`; in `[0, 1]Ł`, `¬a = 1 - a` and `a ⊗ b = max(0, a + b - 1)`, and
`a ⊕ b = ¬(¬a ⊗ ¬b)`, `a → b = ¬a ⊕ b`, `a ∧ b = a ⊗ (a → b)`, `a ∨ b = (a → b) → b`; the
designated value is `1`, and a term is satisfiable when some assignment gives it the value `1`.
On `[0, 1]` these definitions are `a ⊕ b = min(1, a + b)`, `a → b = min(1, 1 - a + b)`,
`a ∧ b = min(a, b)` and `a ∨ b = max(a, b)`, the closed forms `eval` uses.

The formula is written in postfix (reverse Polish) notation as a list of tokens: `0` is `¬`
(unary); `1`, `2`, `3`, `4`, `5` are `⊕`, `⊗`, `→`, `∧`, `∨` (binary, applied to the two most
recent subformulas in their written order); `6` and `7` are the constants `0` and `1`; and
`k + 8` is the variable `xₖ`. `parse` reads the tokens with a stack into `MVTerm`; a token list
is a formula exactly when `parse` returns one.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Terms in the language of MV-algebras `⟨⊕, ⊗, ¬, →, 0, 1, ∧, ∨⟩` over variables `xₖ`. -/
inductive MVTerm : Type where
  | var (k : ℕ) : MVTerm
  | zero : MVTerm
  | one : MVTerm
  | neg (φ : MVTerm) : MVTerm
  | oplus (φ ψ : MVTerm) : MVTerm
  | otimes (φ ψ : MVTerm) : MVTerm
  | imp (φ ψ : MVTerm) : MVTerm
  | wedge (φ ψ : MVTerm) : MVTerm
  | vee (φ ψ : MVTerm) : MVTerm
  deriving DecidableEq

/-- The value of a term in the standard MV-algebra `[0, 1]Ł` under an assignment `σ` of the
variables: `¬a = 1 - a`, `a ⊕ b = min(1, a + b)`, `a ⊗ b = max(0, a + b - 1)`,
`a → b = min(1, 1 - a + b)`, `a ∧ b = min(a, b)`, `a ∨ b = max(a, b)`. -/
noncomputable def eval (σ : ℕ → ℝ) : MVTerm → ℝ
  | .var k => σ k
  | .zero => 0
  | .one => 1
  | .neg φ => 1 - eval σ φ
  | .oplus φ ψ => min 1 (eval σ φ + eval σ ψ)
  | .otimes φ ψ => max 0 (eval σ φ + eval σ ψ - 1)
  | .imp φ ψ => min 1 (1 - eval σ φ + eval σ ψ)
  | .wedge φ ψ => min (eval σ φ) (eval σ ψ)
  | .vee φ ψ => max (eval σ φ) (eval σ ψ)

/-- An instance: the formula as a postfix token list. -/
abbrev LukasiewiczSatisfiabilityInstance := List ℕ

/-- Apply the binary connective with token code `c` (`1`-`5`: `⊕`, `⊗`, `→`, `∧`, `∨`). -/
def binary : ℕ → MVTerm → MVTerm → Option MVTerm
  | 1, φ, ψ => some (.oplus φ ψ)
  | 2, φ, ψ => some (.otimes φ ψ)
  | 3, φ, ψ => some (.imp φ ψ)
  | 4, φ, ψ => some (.wedge φ ψ)
  | 5, φ, ψ => some (.vee φ ψ)
  | _, _, _ => none

/-- Read a postfix token list onto a stack of terms: `0` pops `φ` and pushes `¬φ`; a binary
code `c ∈ {1, …, 5}` pops `ψ` and `φ` and pushes `φ ∘ ψ` for its connective `∘`; `6` and `7`
push the constants `0` and `1`; and `k + 8` pushes `xₖ`. The result is the single term left on
the stack, or `none` when a token lacks its operands or more than one term is left. -/
def parse : List ℕ → List MVTerm → Option MVTerm
  | [], [φ] => some φ
  | [], _ => none
  | 0 :: rest, φ :: stack => parse rest (.neg φ :: stack)
  | 6 :: rest, stack => parse rest (.zero :: stack)
  | 7 :: rest, stack => parse rest (.one :: stack)
  | (k + 8) :: rest, stack => parse rest (.var k :: stack)
  | c :: rest, ψ :: φ :: stack =>
      match binary c φ ψ with
      | some χ => parse rest (χ :: stack)
      | none => none
  | _ :: _, _ => none

/-- Well-formedness of an instance: the tokens form a formula. -/
def WellFormed (i : LukasiewiczSatisfiabilityInstance) : Prop :=
  (parse i []).isSome

/-- Some assignment of values in `[0, 1]` to the variables gives the formula the value `1`. -/
def LukasiewiczSatisfiabilityFeasible (i : LukasiewiczSatisfiabilityInstance) : Prop :=
  ∃ φ, parse i [] = some φ ∧ ∃ σ : ℕ → ℝ, (∀ k, σ k ∈ Set.Icc (0 : ℝ) 1) ∧ eval σ φ = 1

open Classical in
/-- ŁUKASIEWICZ LOGIC SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def lukasiewiczSatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LukasiewiczSatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ LukasiewiczSatisfiabilityFeasible i)
  | none => false

/-- **ŁUKASIEWICZ LOGIC SATISFIABILITY is NP-complete.** Source: Mundici (1987); language and
semantics as in Haniková and Jankovec (2026), Section 2. -/
public theorem_wanted lukasiewiczSatisfiability_npComplete :
    lukasiewiczSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lukasiewiczSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.LukasiewiczSatisfiability
