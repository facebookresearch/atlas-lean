/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Terms
public import CSLibExt.Languages.LambdaCalculus.FOmega.Conversion

/-! # Pure Fω typing with proved type-beta conversion

Type abstraction weakens the existing term context. Type application may
instantiate a binder at any kind-correct operator, including quantified ones.
The sixth rule changes the result only by the proved type-beta conversion.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

/-- **Typing rules of pure Fω.**
The five pure term rules and the type-beta conversion rule of Fω. -/
inductive Typing : {Δ : List Kind} → {m : Nat} →
    Ctx Δ m → Tm Δ m → Ty Δ .star → Prop where
  | var {Δ : List Kind} {m : Nat} {Γ : Ctx Δ m} (i : Fin m) :
      Typing Γ (.var i) (Γ i)
  | lam {Δ : List Kind} {m : Nat} {Γ : Ctx Δ m}
      {A B : Ty Δ .star} {b : Tm Δ (m + 1)} :
      Typing (Fin.cases A Γ) b B → Typing Γ (.lam A b) (.arr A B)
  | app {Δ : List Kind} {m : Nat} {Γ : Ctx Δ m}
      {A B : Ty Δ .star} {f a : Tm Δ m} :
      Typing Γ f (.arr A B) → Typing Γ a A → Typing Γ (.app f a) B
  | tabs {Δ : List Kind} {m : Nat} {κ : Kind} {Γ : Ctx Δ m}
      {b : Tm (κ :: Δ) m} {C : Ty (κ :: Δ) .star} :
      Typing (fun i => (Γ i).rename KVar.succ) b C →
      Typing Γ (.tabs b) (.all C)
  | tapp {Δ : List Kind} {m : Nat} {κ : Kind} {Γ : Ctx Δ m}
      {f : Tm Δ m} {A : Ty Δ κ} {C : Ty (κ :: Δ) .star} :
      Typing Γ f (.all C) → Typing Γ (.tapp f A) (C.instantiate A)
  | conv {Δ : List Kind} {m : Nat} {Γ : Ctx Δ m}
      {t : Tm Δ m} {A B : Ty Δ .star} :
      Typing Γ t A → Ty.Conv A B → Typing Γ t B

variable {Δ : List Kind} {m : Nat} {Γ : Ctx Δ m}
  {t : Tm Δ m} {A : Ty Δ .star}

namespace Typing

/-- **Type substitution preserves Fω typing.**
Kind-correct type substitution preserves typing in arbitrary contexts. -/
theorem tySubst {Ε : List Kind} (h : Typing Γ t A) (σ : Ty.Sub Δ Ε) :
    Typing (fun i => (Γ i).subst σ) (t.tySubst σ) (A.subst σ) := by
  induction h generalizing Ε with
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
  | conv ht hc ih => exact .conv (ih σ) (hc.subst σ)

/-- **Type renaming preserves Fω typing.** Kind-preserving type renaming preserves typing. -/
theorem tyRename {Ε : List Kind} (h : Typing Γ t A) (ρ : KRen Δ Ε) :
    Typing (fun i => (Γ i).rename ρ) (t.tyRename ρ) (A.rename ρ) := by
  simpa only [Tm.tyRename, Ty.subst_var_rename] using
    h.tySubst (fun {_} x => .var (ρ x))

/-- **Term renaming preserves Fω typing.**
A context-respecting term-variable renaming preserves the result type. -/
theorem rename {k : Nat} {Ξ : Ctx Δ k} (h : Typing Γ t A)
    (ρ : Fin m → Fin k) (hρ : ∀ i, Ξ (ρ i) = Γ i) :
    Typing Ξ (t.rename ρ) A := by
  induction h generalizing k with
  | var i =>
    rw [Tm.rename, ← hρ i]
    exact .var (ρ i)
  | lam hb ih =>
    apply Typing.lam
    apply ih (SystemF.liftRen ρ)
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact hρ i
  | app hf ha ihf iha => exact .app (ihf ρ hρ) (iha ρ hρ)
  | tabs hb ih =>
    apply Typing.tabs
    exact ih ρ (fun i => congrArg (Ty.rename KVar.succ) (hρ i))
  | tapp hf ih => exact .tapp (ih ρ hρ)
  | conv ht hc ih => exact .conv (ih ρ hρ) hc

/-- **Term substitution preserves Fω typing.**
Arbitrary correctly typed term substitution preserves typing. -/
theorem subst {k : Nat} {Ξ : Ctx Δ k} (h : Typing Γ t A)
    (σ : Fin m → Tm Δ k) (hσ : ∀ i, Typing Ξ (σ i) (Γ i)) :
    Typing Ξ (t.subst σ) A := by
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
    exact ih (fun i => (σ i).tyRename KVar.succ)
      (fun i => (hσ i).tyRename KVar.succ)
  | tapp hf ih => exact .tapp (ih σ hσ)
  | conv ht hc ih => exact .conv (ih σ hσ) hc

/-- **Term-binder instantiation preserves Fω typing.**
Discharging a typed term binder retains the body result type. -/
theorem instantiate {B : Ty Δ .star} {b : Tm Δ (m + 1)} {a : Tm Δ m}
    (hb : Typing (Fin.cases A Γ) b B) (ha : Typing Γ a A) :
    Typing Γ (b.instantiate a) B := by
  apply hb.subst (Fin.cases a Tm.var)
  intro i
  induction i using Fin.cases with
  | zero => exact ha
  | succ i => exact .var i

/-- **Type-binder instantiation preserves Fω typing.**
Discharging a type binder substitutes its result and restores context. -/
theorem tyInstantiate {κ : Kind} {b : Tm (κ :: Δ) m}
    {C : Ty (κ :: Δ) .star}
    (hb : Typing (fun i => (Γ i).rename KVar.succ) b C) (a : Ty Δ κ) :
    Typing Γ (b.tySubst (Ty.single a)) (C.instantiate a) := by
  have h := hb.tySubst (Ty.single a)
  change Typing (fun i => ((Γ i).rename KVar.succ).instantiate a)
    (b.tySubst (Ty.single a)) (C.instantiate a) at h
  simpa only [Ty.instantiate_rename_succ] using h

end Typing

end Cslib.Languages.LambdaCalculus.FOmega
