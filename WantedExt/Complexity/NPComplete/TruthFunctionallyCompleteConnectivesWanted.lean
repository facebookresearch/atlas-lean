/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO10] TRUTH-FUNCTIONALLY COMPLETE
CONNECTIVES, p. 261 (reference: R. Statman (1976), private communication; transformation from
3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.NonTautologyWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives

open Cslib.Logic.PL

/-!
# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES is NP-complete

INSTANCE: a set `U` of variables and a collection `C` of well-formed Boolean expressions over
`U`. QUESTION: is `C` truth-functionally complete, i.e., is there a truth-functionally complete
set of logical connectives (unary and binary operators) `D = {θ₁, …, θₖ}` such that for each
`θᵢ ∈ D` there is an expression `E ∈ C` and a substitution `s : U → {a, b}` for which
`s(E) ≡ a θᵢ b` or `s(E) ≡ θᵢ a` (depending on whether `θᵢ` is binary or unary)?

Expressions are those of `NonTautologyWanted` (connectives `¬`, `∧`, `∨`, `→`, written in
postfix over `U = {u₀, …, u_{n-1}}`), and `C` is a list of their token lists. A substitution is
`s : ℕ → Bool`, sending `uₓ` to `a` when `s x = true` and to `b` when `s x = false`;
`substOp E s` is the binary truth function `(a, b) ↦ s(E)`, so `s(E) ≡ a θ b` says
`substOp E s = θ`. A unary connective `θ` is represented by the binary truth function
`fun a _ => θ a`, which composes exactly as `θ` does; then `s(E) ≡ θ a` again says
`substOp E s = fun a _ => θ a`. A set `D` of connectives is truth-functionally complete when
every truth function of every arity `m ≥ 1` is a composition of members of `D` applied to the
`m` arguments (`Composed`); arity `0` is excluded because a composition of unary and binary
connectives always mentions an argument.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables `u₀, …, u_{n-1}`, and the expressions of `C`, each
a postfix token list as in `NonTautologyWanted`. -/
abbrev TruthFunctionallyCompleteConnectivesInstance := ℕ × List (List (ℕ × ℕ))

/-- The binary truth function `(a, b) ↦ s(E)` that the expression `E` defines under the
substitution `s`, which sends `uₓ` to `a` if `s x = true` and to `b` if `s x = false`. -/
def substOp (E : Proposition (WithBot ℕ)) (s : ℕ → Bool) (a b : Bool) : Bool :=
  E.evalBool (NonTautology.valuation fun x => if s x then a else b)

/-- `Composed D m f`: the `m`-ary truth function `f` is a composition of the binary connectives
in `D`, i.e., it is built from the projections `x ↦ xⱼ` by applying members of `D`. -/
inductive Composed (D : List (Bool → Bool → Bool)) (m : ℕ) : ((Fin m → Bool) → Bool) → Prop
  | proj (j : Fin m) : Composed D m fun x => x j
  | app {θ : Bool → Bool → Bool} (hθ : θ ∈ D) {f g : (Fin m → Bool) → Bool} :
      Composed D m f → Composed D m g → Composed D m fun x => θ (f x) (g x)

/-- A set `D` of connectives is truth-functionally complete: every truth function of every
arity `m ≥ 1` is a composition of members of `D`. -/
def TruthFunctionallyComplete (D : List (Bool → Bool → Bool)) : Prop :=
  ∀ m, 0 < m → ∀ f : (Fin m → Bool) → Bool, Composed D m f

/-- Well-formedness of an instance: every member of `C` is an expression over
`u₀, …, u_{n-1}` (`NonTautology.WellFormed`). -/
def WellFormed (i : TruthFunctionallyCompleteConnectivesInstance) : Prop :=
  ∀ t ∈ i.2, NonTautology.WellFormed (i.1, t)

/-- Some truth-functionally complete set `D` of connectives has every member defined by an
expression of `C` under a substitution `s : U → {a, b}`. -/
def TruthFunctionallyCompleteConnectivesFeasible
    (i : TruthFunctionallyCompleteConnectivesInstance) : Prop :=
  ∃ D : List (Bool → Bool → Bool), TruthFunctionallyComplete D ∧
    ∀ θ ∈ D, ∃ t ∈ i.2, ∃ E, NonTautology.parse t = some E ∧
      ∃ s : ℕ → Bool, substOp E s = θ

open Classical in
/-- TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES as a decision problem over bitstrings. -/
noncomputable def truthFunctionallyCompleteConnectivesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TruthFunctionallyCompleteConnectivesInstance) x with
  | some i => decide (WellFormed i ∧ TruthFunctionallyCompleteConnectivesFeasible i)
  | none => false

/-- **TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES is NP-complete.** Source: Garey and Johnson
(1979), [LO10] (Statman, 1976). -/
public theorem_wanted truthFunctionallyCompleteConnectives_npComplete :
    truthFunctionallyCompleteConnectivesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L truthFunctionallyCompleteConnectivesDec

end MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives
