/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.ErasureSyntax
public import CSLibExt.Languages.LambdaCalculus.SystemF.Erasure

/-! # Fω closing instances in the single existing term model

The same-project System F closing and beta interfaces close the proved syntax
adapter. Neither an untyped calculus nor a binary relation model is duplicated.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega.Tm

variable {Δ Ε : List Kind} {m k : Nat}

/-- Close scoped Fω variables in exactly the existing System F term model. -/
def close (σ : Fin m → SystemF.Model) (t : Tm Δ m) : SystemF.Model :=
  SystemF.Tm.close σ (eraseSyntax t)

/-- Erase a closed-term Fω expression, with an arbitrary type telescope. -/
def eraseModel (t : Tm Δ 0) : SystemF.Model := close Fin.elim0 t

/-- Closing a variable returns its actual model environment image. -/
@[simp] theorem close_var (σ : Fin m → SystemF.Model) (i : Fin m) :
    close σ (.var i : Tm Δ m) = σ i := rfl

/-- Closing preserves the existing model application constructor. -/
@[simp] theorem close_app (σ : Fin m → SystemF.Model) (f a : Tm Δ m) :
    close σ (.app f a) = SystemF.Model.app (close σ f) (close σ a) := rfl

/-- Type abstraction adds no binder to an erased closing instance. -/
@[simp] theorem close_tabs {κ : Kind} (σ : Fin m → SystemF.Model)
    (b : Tm (κ :: Δ) m) : close σ (.tabs b) = close σ b := rfl

/-- Type application adds no application to an erased closing instance. -/
@[simp] theorem close_tapp {κ : Kind} (σ : Fin m → SystemF.Model)
    (f : Tm Δ m) (A : Ty Δ κ) : close σ (.tapp f A) = close σ f := rfl

/-- Any kind-correct type substitution leaves closing instances unchanged. -/
@[simp] theorem close_tySubst (σ : Ty.Sub Δ Ε) (η : Fin m → SystemF.Model)
    (t : Tm Δ m) : close η (tySubst σ t) = close η t := by
  simp only [close, eraseSyntax_tySubst]

/-- Applying an erased Fω lambda beta-converts to its extended body instance. -/
theorem close_beta (σ : Fin m → SystemF.Model) (A : Ty Δ .star)
    (b : Tm Δ (m + 1)) (a : SystemF.Model) :
    SystemF.BetaEq (SystemF.Model.app (close σ (.lam A b)) a)
      (close (Fin.cases a σ) b) :=
  SystemF.Tm.close_beta σ (.all (.var 0)) (eraseSyntax b) a

/-- Closing composes actual Fω term substitutions with model environments. -/
theorem close_subst (σ : Fin m → Tm Δ k) (η : Fin k → SystemF.Model)
    (t : Tm Δ m) :
    close η (subst σ t) = close (fun i => close η (σ i)) t := by
  simp only [close, eraseSyntax_subst, SystemF.Tm.close_subst]

/-- Actual term-binder discharge extends the same model closing environment. -/
theorem close_instantiate (η : Fin m → SystemF.Model)
    (b : Tm Δ (m + 1)) (a : Tm Δ m) :
    close η (instantiate b a) = close (Fin.cases (close η a) η) b := by
  simp only [close, eraseSyntax_instantiate, SystemF.Tm.close_instantiate]

end Cslib.Languages.LambdaCalculus.FOmega.Tm
