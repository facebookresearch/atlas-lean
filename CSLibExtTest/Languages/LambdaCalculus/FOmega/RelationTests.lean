/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.FOmega.RelationalTypes

/-! # Genuine relation-carrier and higher-kind quantification probes -/

open Cslib.Languages.LambdaCalculus.FOmega

private def env : KEnv Cslib.Languages.LambdaCalculus.SystemF.Rel [] :=
  fun {_} x => nomatch x

open Cslib.Languages.LambdaCalculus.SystemF (Model BetaEq)

example (f g : Model) :
    ¬ ((Ty.all (κ := .star) (.var .zero) : Ty [] .star).interpret env).holds f g := by
  intro h
  change ∀ R : Cslib.Languages.LambdaCalculus.SystemF.Rel, R.holds f g at h
  exact h Cslib.Languages.LambdaCalculus.SystemF.Rel.empty

example (x : Model) :
    (Cslib.Languages.LambdaCalculus.SystemF.Rel.betaClass x).holds x x :=
  ⟨BetaEq.refl x, BetaEq.refl x⟩

example (f g : Model) :
    (Cslib.Languages.LambdaCalculus.SystemF.Rel.total).holds f g := True.intro

private def higherResult : Ty [] .star :=
  .all (κ := .arrow .star .star)
    (.all (κ := .star) (.app (.var (.succ .zero)) (.var .zero)))

example (f g : Model) : ¬ (higherResult.interpret env).holds f g := by
  intro h
  change ∀ F : Cslib.Languages.LambdaCalculus.SystemF.Rel →
    Cslib.Languages.LambdaCalculus.SystemF.Rel,
    ∀ R, (F R).holds f g at h
  exact h (fun _ => Cslib.Languages.LambdaCalculus.SystemF.Rel.empty)
    Cslib.Languages.LambdaCalculus.SystemF.Rel.total
