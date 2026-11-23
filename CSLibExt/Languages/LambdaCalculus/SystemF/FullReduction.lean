/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.Typing

/-!
# Full reduction and subject reduction for pure System F

`FullStep` is one step of full reduction on the scoped terms of
`SystemF.Syntax`: term beta and type beta may fire at any position,
including under term and type binders, and term beta places no value
restriction on its argument. Contracting a redex reuses the existing
capture-avoiding operations `Tm.instantiate` and `Tm.tySubst`.

`FullStep.preservation` is subject reduction for this relation in arbitrary
open contexts, from the substitution lemmas `Typing.instantiate` and
`Typing.tyInstantiate`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- One step of full reduction: term beta and type beta in any context,
including under term and type binders. -/
inductive FullStep : {n m : Nat} → Tm n m → Tm n m → Prop where
  | beta {n m : Nat} {A : Ty n} {b : Tm n (m + 1)} {a : Tm n m} :
      FullStep (.app (.lam A b) a) (b.instantiate a)
  | tyBeta {n m : Nat} {b : Tm (n + 1) m} {A : Ty n} :
      FullStep (.tapp (.tabs b) A) (b.tySubst (Fin.cases A Ty.var))
  | lam {n m : Nat} {A : Ty n} {b b' : Tm n (m + 1)} :
      FullStep b b' → FullStep (.lam A b) (.lam A b')
  | appFun {n m : Nat} {f f' a : Tm n m} :
      FullStep f f' → FullStep (.app f a) (.app f' a)
  | appArg {n m : Nat} {f a a' : Tm n m} :
      FullStep a a' → FullStep (.app f a) (.app f a')
  | tabs {n m : Nat} {b b' : Tm (n + 1) m} :
      FullStep b b' → FullStep (.tabs b) (.tabs b')
  | tappFun {n m : Nat} {f f' : Tm n m} {A : Ty n} :
      FullStep f f' → FullStep (.tapp f A) (.tapp f' A)

namespace FullStep

variable {n m : Nat} {Γ : Ctx n m} {A : Ty n} {t t' : Tm n m}

/-- Subject reduction: a full-reduction step preserves the exact type in
arbitrary open contexts. -/
theorem preservation (ht : Typing Γ t A) (hs : FullStep t t') :
    Typing Γ t' A := by
  induction hs with
  | beta =>
    cases ht with
    | app hf ha => cases hf with
      | lam hb => exact hb.instantiate ha
  | tyBeta =>
    cases ht with
    | tapp hf => cases hf with
      | tabs hb => exact hb.tyInstantiate _
  | lam hs ih =>
    cases ht with
    | lam hb => exact .lam (ih hb)
  | appFun hs ih =>
    cases ht with
    | app hf ha => exact .app (ih hf) ha
  | appArg hs ih =>
    cases ht with
    | app hf ha => exact .app hf (ih ha)
  | tabs hs ih =>
    cases ht with
    | tabs hb => exact .tabs (ih hb)
  | tappFun hs ih =>
    cases ht with
    | tapp hf => exact .tapp (ih hf)

end FullStep

end Cslib.Languages.LambdaCalculus.SystemF
