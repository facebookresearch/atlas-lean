/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LAMBEK CALCULUS DERIVABILITY is NP-complete

Source:
M. Pentus, "Lambek calculus is NP-complete", Theoretical Computer Science 357 (2006), 186-201,
doi:10.1016/j.tcs.2006.03.018.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LambekCalculusDerivability

/-!
# LAMBEK CALCULUS DERIVABILITY is NP-complete

INSTANCE: a sequent `Γ → A` of the Lambek calculus `L`, where `Γ` is a finite sequence of types
and `A` is a type, types being built from primitive types `p₀, p₁, …` with the binary
connectives `·` (product), `/` and `\`. QUESTION: is `Γ → A` derivable in `L`?

Pentus (Section 1) defines the Lambek calculus allowing empty premises `L*` by the axioms
`A → A` and the rules (CUT), `(→/)`, `(/→)`, `(→\)`, `(\→)`, `(→·)` and `(·→)`, and `L`, Lambek's
original syntactic calculus, as the same calculus in which `(→\)` and `(→/)` require their
premise context `Π` to be nonempty. He proves that the derivability problem is NP-complete for
both `L` and `L*` (abstract). This module states the result for `L`. `Derivable` is Pentus's
calculus for `L`, rule for rule, with the cut rule included as in the source (the
cut-elimination theorem holds for `L`, so the derivable sequents are the same without it).

A type is written in postfix (reverse Polish) notation as a list of tokens: `0` is `·`, `1` is
`/` and `2` is `\` (binary, applied to the two most recent subtypes in their written order, so
`B A 1` is `B / A` and `A B 2` is `A \ B`), and `k + 3` is the primitive type `pₖ`. `parse`
reads the tokens with a stack into `LType`. The sequent is a list of token lists for the types of
`Γ`, in order, and a token list for `A`; it is well formed when every token list is a type.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Types of the Lambek calculus: primitive types `pₖ`, products `A · B`, and the divisions
`B / A` (`over B A`) and `A \ B` (`under A B`). -/
inductive LType : Type where
  | prim (k : ℕ) : LType
  | mul (A B : LType) : LType
  | over (B A : LType) : LType
  | under (A B : LType) : LType
  deriving DecidableEq

/-- Derivability `L ⊢ Γ → A` in the Lambek calculus `L` (Pentus, Section 1): the axiom
`A → A`, the cut rule, and the left and right rules for `/`, `\` and `·`; the right rules for
`/` and `\` require a nonempty context `Π`. -/
inductive Derivable : List LType → LType → Prop where
  /-- `A → A`. -/
  | ax (A : LType) : Derivable [A] A
  /-- (CUT): from `Φ → B` and `Γ B Δ → A` infer `Γ Φ Δ → A`. -/
  | cut {Φ Γ Δ : List LType} {A B : LType} :
      Derivable Φ B → Derivable (Γ ++ B :: Δ) A → Derivable (Γ ++ Φ ++ Δ) A
  /-- `(→/)`: from `Π A → B` infer `Π → B / A`, for nonempty `Π` (named `Ψ` here, since `Π` is
  reserved syntax). -/
  | rightOver {Ψ : List LType} {A B : LType} :
      Ψ ≠ [] → Derivable (Ψ ++ [A]) B → Derivable Ψ (.over B A)
  /-- `(/→)`: from `Φ → A` and `Γ B Δ → C` infer `Γ (B / A) Φ Δ → C`. -/
  | leftOver {Φ Γ Δ : List LType} {A B C : LType} :
      Derivable Φ A → Derivable (Γ ++ B :: Δ) C → Derivable (Γ ++ .over B A :: Φ ++ Δ) C
  /-- `(→\)`: from `A Π → B` infer `Π → A \ B`, for nonempty `Π` (named `Ψ` here). -/
  | rightUnder {Ψ : List LType} {A B : LType} :
      Ψ ≠ [] → Derivable (A :: Ψ) B → Derivable Ψ (.under A B)
  /-- `(\→)`: from `Φ → A` and `Γ B Δ → C` infer `Γ Φ (A \ B) Δ → C`. -/
  | leftUnder {Φ Γ Δ : List LType} {A B C : LType} :
      Derivable Φ A → Derivable (Γ ++ B :: Δ) C → Derivable (Γ ++ Φ ++ .under A B :: Δ) C
  /-- `(→·)`: from `Γ → A` and `Δ → B` infer `Γ Δ → A · B`. -/
  | rightMul {Γ Δ : List LType} {A B : LType} :
      Derivable Γ A → Derivable Δ B → Derivable (Γ ++ Δ) (.mul A B)
  /-- `(·→)`: from `Γ A B Δ → C` infer `Γ (A · B) Δ → C`. -/
  | leftMul {Γ Δ : List LType} {A B C : LType} :
      Derivable (Γ ++ A :: B :: Δ) C → Derivable (Γ ++ .mul A B :: Δ) C

/-- An instance: the token lists of the types of `Γ`, in order, and the token list of `A`. -/
abbrev LambekCalculusDerivabilityInstance := List (List ℕ) × List ℕ

/-- Read a postfix token list onto a stack of types: `0`, `1`, `2` pop `Y` and `X` and push
`X · Y`, `X / Y` and `X \ Y`, and `k + 3` pushes `pₖ`. The result is the single type left on the
stack, or `none` when a token lacks its operands or more than one type is left. -/
def parse : List ℕ → List LType → Option LType
  | [], [X] => some X
  | [], _ => none
  | 0 :: rest, Y :: X :: stack => parse rest (.mul X Y :: stack)
  | 1 :: rest, Y :: X :: stack => parse rest (.over X Y :: stack)
  | 2 :: rest, Y :: X :: stack => parse rest (.under X Y :: stack)
  | (k + 3) :: rest, stack => parse rest (.prim k :: stack)
  | _ :: _, _ => none

/-- Well-formedness of an instance: every token list is a type. -/
def WellFormed (i : LambekCalculusDerivabilityInstance) : Prop :=
  (∀ t ∈ i.1, (parse t []).isSome) ∧ (parse i.2 []).isSome

/-- The sequent `Γ → A` spelled by the instance is derivable in `L`. -/
def LambekCalculusDerivabilityFeasible (i : LambekCalculusDerivabilityInstance) : Prop :=
  ∃ Γ A, i.1.mapM (fun t => parse t []) = some Γ ∧ parse i.2 [] = some A ∧ Derivable Γ A

open Classical in
/-- LAMBEK CALCULUS DERIVABILITY as a decision problem over bitstrings. -/
noncomputable def lambekCalculusDerivabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LambekCalculusDerivabilityInstance) x with
  | some i => decide (WellFormed i ∧ LambekCalculusDerivabilityFeasible i)
  | none => false

/-- **LAMBEK CALCULUS DERIVABILITY is NP-complete.** Source: Pentus (2006). -/
public theorem_wanted lambekCalculusDerivability_npComplete :
    lambekCalculusDerivabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lambekCalculusDerivabilityDec

end MetaMathlibExt.Complexity.NPComplete.LambekCalculusDerivability
