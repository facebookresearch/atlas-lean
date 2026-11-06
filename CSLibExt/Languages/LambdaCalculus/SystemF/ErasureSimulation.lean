/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.Erasure
public import CSLibExt.Languages.LambdaCalculus.SystemF.Semantics

/-!
# The call-by-value erasure bridge

Actual term beta substitution erases to upstream beta conversion. Actual type
beta substitution has identical erasures. The contextual CBV rules preserve
conversion. The bridge works under arbitrary model-valued closing environments,
for open and closed scoped terms. It does not assert termination.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- **Erasure of a System F evaluation step is a beta conversion.**
Actual CBV steps preserve beta conversion of closing instances. -/
theorem erasure_step {n m : Nat} {t t' : Tm n m} (hs : Step t t')
    (σ : Fin m → Model) : BetaEq (Tm.close σ t) (Tm.close σ t') := by
  induction hs with
  | @appFun f f' a hs ih => exact ih.appFun (Tm.close σ a)
  | @appArg f a a' hv hs ih => exact BetaEq.appArg (Tm.close σ f) ih
  | @beta A b a hv =>
    rw [Tm.close_app, Tm.close_instantiate]
    exact Tm.close_beta σ A b (Tm.close σ a)
  | tappFun hs ih => exact ih
  | tyBeta =>
    rw [Tm.close_tapp, Tm.close_tabs, Tm.close_tySubst]
    exact BetaEq.refl _

/-- **Erasure of multistep System F evaluation is a beta conversion.**
Finite CBV evaluation preserves conversion of erased instances. -/
theorem erasure_steps {n m : Nat} {t t' : Tm n m} (hs : Steps t t')
    (σ : Fin m → Model) : BetaEq (Tm.close σ t) (Tm.close σ t') := by
  induction hs with
  | refl => exact BetaEq.refl _
  | tail hs hstep ih => exact ih.trans (erasure_step hstep σ)

end Cslib.Languages.LambdaCalculus.SystemF
