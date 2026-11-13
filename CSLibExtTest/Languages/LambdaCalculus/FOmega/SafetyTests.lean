/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.FOmega.Safety

/-! # Higher-kind typing and conversion-aware CBV consumers -/

open Cslib.Languages.LambdaCalculus.FOmega

private def empty {Δ : List Kind} : Ctx Δ 0 := Fin.elim0

private def applied : Ty [.star, .arrow .star .star] .star :=
  .app (.var (.succ .zero)) (.var .zero)

private def higherIdType : Ty [] .star :=
  .all (κ := .arrow .star .star) (.all (κ := .star) (.arr applied applied))

private def higherIdBody : Tm [.arrow .star .star] 0 :=
  .tabs (κ := .star) (.lam applied (.var 0))

private def higherId : Tm [] 0 := .tabs higherIdBody

private theorem higherId_typing : Typing empty higherId higherIdType :=
  .tabs (.tabs (.lam (.var 0)))

example : Value higherId ∨ ∃ t', Step higherId t' := higherId_typing.progress

private def opId {Δ : List Kind} : Ty Δ (.arrow .star .star) :=
  .lam (.var .zero)

private def poly : Ty [] .star :=
  .all (κ := .star) (.arr (.var .zero) (.var .zero))

private def instanceTerm : Tm [] 0 := .tapp (.tapp higherId opId) poly

private theorem instance_typing : Typing empty instanceTerm (.arr poly poly) :=
  .conv (.tapp (.tapp higherId_typing)) (.arr (.beta _ _) (.beta _ _))

example : Value instanceTerm ∨ ∃ t', Step instanceTerm t' :=
  instance_typing.progress

example : Relation.ReflTransGen Step instanceTerm
    (.lam (.app opId poly) (.var 0)) :=
  (Relation.ReflTransGen.single (.tapp (.tybeta higherIdBody opId))).tail
    (.tybeta _ poly)

example : Typing empty (.lam (.app opId poly) (.var 0)) (.arr poly poly) :=
  instance_typing.preservation_steps
    ((Relation.ReflTransGen.single (.tapp (.tybeta higherIdBody opId))).tail
      (.tybeta _ poly))

example {Δ : List Kind} (A : Ty Δ .star) :
    Value (.lam A (.var 0) : Tm Δ 0) ∨
      ∃ t', Step (.lam A (.var 0) : Tm Δ 0) t' :=
  (Typing.lam (Typing.var (Γ := Fin.cases A empty) 0)).progress

example :
    Tm.subst (fun _ : Fin 1 => .lam (.var .zero) (.var 0) : Fin 1 → Tm [.star] 0)
      (.tabs (κ := .star) (.var 0) : Tm [.star] 1) =
    (.tabs (κ := .star) (.lam (.var (.succ .zero)) (.var 0)) : Tm [.star] 0) := rfl

example {Δ : List Kind} (A : Ty Δ .star) :
    Tm.subst (fun _ : Fin 1 => .var 0 : Fin 1 → Tm Δ 1)
      (.lam A (.var 1)) = (.lam A (.var 1) : Tm Δ 1) := rfl
