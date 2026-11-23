/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Closing
public import CSLibExt.Languages.LambdaCalculus.FOmega.Safety

/-! # Fω weak-CBV erasure into the existing full-beta term model

Actual term substitution uses the banked closing/beta laws; arbitrary-kinded
type substitution has identical erasures. This proves conversion, not CBV
termination or type-operator normalization.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

/-- Every actual Fω CBV step preserves beta conversion of arbitrary closing instances. -/
theorem erasure_step {Δ : List Kind} {m : Nat} {t t' : Tm Δ m}
    (hs : Step t t') (σ : Fin m → SystemF.Model) :
    SystemF.BetaEq (Tm.close σ t) (Tm.close σ t') := by
  induction hs with
  | appFun hs ih => exact ih.appFun (Tm.close σ _)
  | appArg hv hs ih => exact SystemF.BetaEq.appArg (Tm.close σ _) ih
  | beta hv =>
    rw [Tm.close_app, Tm.close_instantiate]
    exact Tm.close_beta σ _ _ (Tm.close σ _)
  | tapp hs ih => exact ih
  | tybeta =>
    rw [Tm.close_tapp, Tm.close_tabs, Tm.close_tySubst]
    exact SystemF.BetaEq.refl _

/-- Finite Fω evaluation preserves beta conversion of the closing instances. -/
theorem erasure_steps {Δ : List Kind} {m : Nat} {t t' : Tm Δ m}
    (hs : Relation.ReflTransGen Step t t') (σ : Fin m → SystemF.Model) :
    SystemF.BetaEq (Tm.close σ t) (Tm.close σ t') := by
  induction hs with
  | refl => exact SystemF.BetaEq.refl _
  | tail hs p ih => exact ih.trans (erasure_step p σ)

end Cslib.Languages.LambdaCalculus.FOmega
