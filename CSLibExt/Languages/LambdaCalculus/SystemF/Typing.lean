/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.TypeSubstitution

/-!
# The five typing rules of pure System F

Type abstraction weakens the existing term-context types. Type application
admits any well-scoped type argument, including a quantified type. There is
no subsumption or implicit type conversion rule.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- Extrinsic typing of scoped pure System F terms. -/
inductive Typing : {n m : Nat} → Ctx n m → Tm n m → Ty n → Prop where
  | var {n m : Nat} {Γ : Ctx n m} (i : Fin m) :
      Typing Γ (.var i) (Γ i)
  | lam {n m : Nat} {Γ : Ctx n m} {A B : Ty n} {b : Tm n (m + 1)} :
      Typing (Fin.cases A Γ) b B → Typing Γ (.lam A b) (.arr A B)
  | app {n m : Nat} {Γ : Ctx n m} {A B : Ty n} {f a : Tm n m} :
      Typing Γ f (.arr A B) → Typing Γ a A → Typing Γ (.app f a) B
  | tabs {n m : Nat} {Γ : Ctx n m} {b : Tm (n + 1) m} {C : Ty (n + 1)} :
      Typing (fun i => (Γ i).rename Fin.succ) b C →
      Typing Γ (.tabs b) (.all C)
  | tapp {n m : Nat} {Γ : Ctx n m} {f : Tm n m} {A : Ty n}
      {C : Ty (n + 1)} :
      Typing Γ f (.all C) → Typing Γ (.tapp f A) (C.instantiate A)

variable {n m : Nat} {Γ : Ctx n m} {A : Ty n} {t : Tm n m}

namespace Typing

/-- Type substitution preserves typing, including every context type. -/
theorem tySubst {k : Nat} (h : Typing Γ t A) (σ : Fin n → Ty k) :
    Typing (fun i => (Γ i).subst σ) (t.tySubst σ) (A.subst σ) := by
  induction h generalizing k with
  | var i => exact .var i
  | lam hb ih =>
    apply Typing.lam
    convert ih σ using 1
    funext i
    induction i using Fin.cases <;> rfl
  | app hf ha ihf iha => exact .app (ihf σ) (iha σ)
  | tabs hb ih =>
    apply Typing.tabs
    simpa only [Ty.subst_lift_rename] using ih (Ty.liftSub σ)
  | tapp hf ih =>
    rw [Tm.tySubst, Ty.subst_instantiate]
    exact .tapp (ih σ)

/-- Type renaming preserves typing without adding term variables. -/
theorem tyRename {k : Nat} (h : Typing Γ t A) (ρ : Fin n → Fin k) :
    Typing (fun i => (Γ i).rename ρ) (t.tyRename ρ) (A.rename ρ) := by
  simpa only [Tm.tyRename, Ty.subst_var_rename] using
    h.tySubst (fun i => .var (ρ i))

/-- A context-respecting term renaming preserves the type. -/
theorem rename {k : Nat} {Δ : Ctx n k} (h : Typing Γ t A)
    (ρ : Fin m → Fin k) (hρ : ∀ i, Δ (ρ i) = Γ i) :
    Typing Δ (t.rename ρ) A := by
  induction h generalizing k with
  | var i =>
    rw [Tm.rename, ← hρ i]
    exact .var (ρ i)
  | lam hb ih =>
    apply Typing.lam
    apply ih (liftRen ρ)
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact hρ i
  | app hf ha ihf iha => exact .app (ihf ρ hρ) (iha ρ hρ)
  | tabs hb ih =>
    apply Typing.tabs
    exact ih ρ (fun i => congrArg (Ty.rename Fin.succ) (hρ i))
  | tapp hf ih => exact .tapp (ih ρ hρ)

/-- Correctly typed simultaneous term substitution preserves typing. -/
theorem subst {k : Nat} {Δ : Ctx n k} (h : Typing Γ t A)
    (σ : Fin m → Tm n k) (hσ : ∀ i, Typing Δ (σ i) (Γ i)) :
    Typing Δ (t.subst σ) A := by
  induction h generalizing k with
  | var i => exact hσ i
  | lam hb ih =>
    apply Typing.lam
    apply ih (Tm.liftSub σ)
    intro i
    induction i using Fin.cases with
    | zero => exact .var 0
    | succ i => exact (hσ i).rename Fin.succ (fun _ => rfl)
  | app hf ha ihf iha => exact .app (ihf σ hσ) (iha σ hσ)
  | tabs hb ih =>
    apply Typing.tabs
    exact ih (fun i => (σ i).tyRename Fin.succ)
      (fun i => (hσ i).tyRename Fin.succ)
  | tapp hf ih => exact .tapp (ih σ hσ)

/-- Discharging a term binder preserves the body type. -/
theorem instantiate {B : Ty n} {b : Tm n (m + 1)} {a : Tm n m}
    (hb : Typing (Fin.cases A Γ) b B) (ha : Typing Γ a A) :
    Typing Γ (b.instantiate a) B := by
  apply hb.subst (Fin.cases a Tm.var)
  intro i
  induction i using Fin.cases with
  | zero => exact ha
  | succ i => exact .var i

/-- Type binder discharge substitutes the type and restores the context. -/
theorem tyInstantiate {b : Tm (n + 1) m} {C : Ty (n + 1)}
    (hb : Typing (fun i => (Γ i).rename Fin.succ) b C) (A : Ty n) :
    Typing Γ (b.tySubst (Fin.cases A Ty.var)) (C.instantiate A) := by
  have h := hb.tySubst (Fin.cases A Ty.var)
  change Typing (fun i => ((Γ i).rename Fin.succ).instantiate A)
    (b.tySubst (Fin.cases A Ty.var)) (C.instantiate A) at h
  simpa only [Ty.instantiate_rename] using h

end Typing

end Cslib.Languages.LambdaCalculus.SystemF
