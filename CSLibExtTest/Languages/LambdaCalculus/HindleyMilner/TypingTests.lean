/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.Typing

@[expose] public section

/-!
# Tests for let-polymorphic typing

Generalization and instantiation on a concrete scheme, the polymorphic identity under `let`
against the untypable λ-bound self-application, and the substitution and generality lemmas
applied to concrete derivations.
-/

set_option autoImplicit false

namespace CSLibExtTest.Languages.LambdaCalculus.HindleyMilner

open Cslib.Unification Cslib.Unification.Term Cslib.HindleyMilner

/-- Base types for the examples. -/
inductive Base where
  | int
  | bool
  deriving DecidableEq, Repr

private def α : Ty Base := var 0
private def int : Ty Base := const .int

-- generalizing `α → α` in the empty context binds `α`; instantiating gives `int → int`
example : gen ([] : Ctx Base) (node α α) = node (const (.inr 0)) (const (.inr 0)) := by
  decide
example : (gen ([] : Ctx Base) (node α α)).inst (fun _ ↦ int) = node int int := by decide
-- a variable free in the context is not generalized
example : gen ([("y", toScheme α)] : Ctx Base) (node α α) = node (var 0) (var 0) := by decide

-- shadowing: only the visible binding of `x` counts, so `var 1` is generalized
example : Ctx.ftv ([("x", toScheme (var 0)), ("x", toScheme (var 1))] : Ctx Base) = {0} := by
  decide
example : gen ([("x", toScheme (var 0)), ("x", toScheme (var 1))] : Ctx Base) (var 1) =
    const (.inr 1) := by
  decide

/-- The identity is polymorphic under `let`. -/
example : HasType ([] : Ctx Base) (.let_ "id" (.lam "x" (.var "x")) (.app (.var "id") (.var "id")))
    (node α α) :=
  hasType_let_id_app_id [] "id" "x" 0

/-- It also works when the result variable is free in the context. -/
example : HasType ([("y", toScheme (var 0))] : Ctx Base)
    (.let_ "id" (.lam "x" (.var "x")) (.app (.var "id") (.var "id"))) (node (var 0) (var 0)) :=
  hasType_let_id_app_id _ "id" "x" 0

/-- The same program with `id` λ-bound instead of `let`-bound has no type: its body is
`λid. id id`. -/
example (τ : Ty Base) :
    ¬ HasType ([] : Ctx Base) (.lam "id" (.app (.var "id") (.var "id"))) τ :=
  not_hasType_lam_self_app [] "id" τ

/-- `λx. x : α → α`, and by the substitution lemma `λx. x : int → int`. -/
example : HasType ([] : Ctx Base) (.lam "x" (.var "x")) (node int int) := by
  have h : HasType ([] : Ctx Base) (.lam "x" (.var "x")) (node α α) := by
    refine HasType.lam ?_
    have h' := HasType.var (Γ := [("x", toScheme α)]) (x := "x") (σ := toScheme α)
      (fun _ ↦ α) (by simp [Ctx.lookup])
    rwa [inst_toScheme] at h'
  simpa [α, int, Ctx.subst] using h.subst fun _ ↦ int

/-- A more general context types more: a polymorphic `f : ∀α. α → α` can play the role of
the monomorphic `f : int → int`. -/
example : HasType ([("f", gen [] (node α α))] : Ctx Base) (.app (.var "f") (.var "f"))
    (node int int) := by
  have h : HasType ([("f", toScheme (node (node int int) (node int int)))] : Ctx Base)
      (.var "f") (node (node int int) (node int int)) := by
    have h' := HasType.var (Γ := [("f", toScheme (node (node int int) (node int int)))])
      (x := "f") (σ := toScheme (node (node int int) (node int int))) (fun _ ↦ int)
      (by simp [Ctx.lookup])
    rwa [inst_toScheme] at h'
  refine HasType.app (τ₁ := node int int) ?_ ?_
  · refine h.mono ((Ctx.MoreGeneral.refl []).cons "f" ⟨fun ts ↦ ⟨fun _ ↦ node int int, ?_⟩, ?_⟩)
    · rw [inst_toScheme]
      decide
    · decide
  · have h' := HasType.var (Γ := [("f", gen [] (node α α))]) (x := "f")
      (σ := gen [] (node α α)) (fun _ ↦ int) (by simp [Ctx.lookup])
    simpa [inst_gen, Ctx.ftv, α, int] using h'

end CSLibExtTest.Languages.LambdaCalculus.HindleyMilner
