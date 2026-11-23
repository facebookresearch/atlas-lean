/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.CurryHoward

/-!
# Tests for the Curry-Howard translation

Positive examples translate closed and open terms into minimal-logic
derivations and check the rule each term constructor becomes. Negative
scoping examples show that a variable is typed by its position in the
context: the empty context has no variables, and under a single binder the
only variable is index `0`, at the binder's type.
-/

open scoped CslibStlc
open Cslib.Logic Cslib.Logic.LegacyPL InferenceSystem

namespace Cslib.Languages.LambdaCalculus.Stlc

namespace CurryHowardTests

/-- A base type. -/
abbrev a : Ty Nat := .base 0

/-- A second base type, distinct from `a`. -/
abbrev b : Ty Nat := .base 1

/-- The identity `λ. 0` at `a`. -/
def idTm : Tm [] (a ⇒ a) := .lam (.var .zero)

/-- The constant combinator `λ. λ. 1` at `a ⇒ b ⇒ a`. -/
def constTm : Tm [] (a ⇒ b ⇒ a) := .lam (.lam (.var (.succ .zero)))

/-- Modus ponens as a term: apply the hypothesis `a ⇒ b` to the hypothesis
`a`. -/
def mpTm : Tm [a ⇒ b, a] b := .app (.var .zero) (.var (.succ .zero))

example : (a ⇒ a).toProp = .imp (.atom 0) (.atom 0) := rfl

example : ctxHyps ([] : List (Ty Nat)) = ∅ := by simp [ctxHyps]

example : ctxHyps [a ⇒ b, a] = {.imp (.atom 0) (.atom 1), .atom 0} := by
  simp [ctxHyps, Ty.toProp]

/-- The identity proves `a → a` in minimal logic from no hypotheses. -/
example : DerivableIn (Theory.MPL Nat) (ctxHyps [] ⊢ (a ⇒ a).toProp) :=
  curry_howard idTm

/-- The constant combinator proves `a → b → a`. -/
example : DerivableIn (Theory.MPL Nat) (ctxHyps [] ⊢ (a ⇒ b ⇒ a).toProp) :=
  curry_howard constTm

/-- An open term proves its type from the hypotheses of its context. -/
example : DerivableIn (Theory.MPL Nat) (ctxHyps [a ⇒ b, a] ⊢ b.toProp) :=
  curry_howard mpTm

/-- A variable becomes an assumption, an application implication
elimination, and an abstraction implication introduction. -/
example {T : Theory Nat} (x : Var [a] a) :
    (Tm.var x).toDerivation (T := T) = .ass x.toProp_mem_ctxHyps := rfl

example {T : Theory Nat} {Γ : List (Ty Nat)} {A B : Ty Nat} (f : Tm Γ (A ⇒ B))
    (x : Tm Γ A) :
    (Tm.app f x).toDerivation (T := T) = .implE f.toDerivation x.toDerivation := rfl

example {T : Theory Nat} : ∃ d, idTm.toDerivation (T := T) = .implI ∅ d :=
  ⟨_, rfl⟩

/-- The empty context has no variables. -/
example (A : Ty Nat) : IsEmpty (Var ([] : List (Ty Nat)) A) :=
  ⟨fun x => nomatch x⟩

/-- Under a single binder, the only variable is index `0`... -/
example (x : Var [a] a) : x = .zero := by
  cases x with
  | zero => rfl
  | succ y => nomatch y

/-- ...and it has the binder's type, so a variable of type `b` in context
`[a]`, or a body `λ. 0 : a ⇒ b`, cannot be formed. -/
example (A B : Ty Nat) (x : Var [A] B) : B = A := by
  cases x with
  | zero => rfl
  | succ y => nomatch y

example : IsEmpty (Var [a] b) :=
  ⟨fun x => match x with | .succ y => nomatch y⟩

end CurryHowardTests

end Cslib.Languages.LambdaCalculus.Stlc
