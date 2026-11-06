/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Syntax

/-! # Capture-avoiding binding laws for kinded type operators -/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega.Ty

variable {Δ Ε Ζ : List Kind} {κ μ : Kind}

/-- **Renaming of type operators depends only on variable images.**
Renaming depends only on its action on kinded variables. -/
theorem rename_congr {ρ τ : KRen Δ Ε}
    (h : ∀ {ν} (x : KVar Δ ν), ρ x = τ x) (t : Ty Δ κ) :
    rename ρ t = rename τ t := by
  have e : @ρ = @τ := by funext ν x; exact h x
  rw [e]

/-- **Identity renaming fixes type operators.** The identity renaming fixes every type operator. -/
@[simp] theorem rename_id (t : Ty Δ κ) :
    rename (fun {_} x => x) t = t := by
  induction t with
  | var => rfl
  | app f a ihf iha | arr f a ihf iha => simp [rename, ihf, iha]
  | lam b ih | all b ih =>
    simp only [rename]
    congr 1
    rw [rename_congr (ρ := KRen.lift (fun {_} x => x))
      (τ := fun {_} x => x) (by intro ν x; cases x <;> rfl), ih]

/-- **Composition of kind-preserving renamings.**
Successive kind-preserving renamings fuse, including beneath binders. -/
theorem rename_rename (ρ : KRen Δ Ε) (τ : KRen Ε Ζ) (t : Ty Δ κ) :
    rename τ (rename ρ t) = rename (fun {_} x => τ (ρ x)) t := by
  induction t generalizing Ε Ζ with
  | var => rfl
  | app f a ihf iha | arr f a ihf iha => simp [rename, ihf, iha]
  | lam b ih | all b ih =>
    simp only [rename]
    congr 1
    rw [ih]
    apply rename_congr
    intro ν x
    cases x <;> rfl

/-- **Substitution of type operators depends only on variable images.**
Substitution depends only on the images of kinded variables. -/
theorem subst_congr {σ τ : Sub Δ Ε}
    (h : ∀ {ν} (x : KVar Δ ν), σ x = τ x) (t : Ty Δ κ) :
    subst σ t = subst τ t := by
  have e : @σ = @τ := by funext ν x; exact h x
  rw [e]

/-- **Identity substitution fixes type operators.**
Substituting each variable by itself fixes every type operator. -/
@[simp] theorem subst_id (t : Ty Δ κ) : subst Ty.var t = t := by
  induction t with
  | var => rfl
  | app f a ihf iha | arr f a ihf iha => simp [subst, ihf, iha]
  | lam b ih | all b ih =>
    simp only [subst]
    congr 1
    rw [subst_congr (σ := liftSub Ty.var) (τ := Ty.var)
      (by intro ν x; cases x <;> rfl), ih]

/-- **Substitution after renaming of type operators.**
Substitution after renaming is precomposition on the variable images. -/
theorem subst_rename (ρ : KRen Δ Ε) (σ : Sub Ε Ζ) (t : Ty Δ κ) :
    subst σ (rename ρ t) = subst (fun {_} x => σ (ρ x)) t := by
  induction t generalizing Ε Ζ with
  | var => rfl
  | app f a ihf iha | arr f a ihf iha => simp [rename, subst, ihf, iha]
  | lam b ih | all b ih =>
    simp only [rename, subst]
    congr 1
    rw [ih]
    apply subst_congr
    intro ν x
    cases x <;> rfl

/-- **Renaming after substitution of type operators.**
Renaming after substitution renames each substituted type operator. -/
theorem rename_subst (σ : Sub Δ Ε) (ρ : KRen Ε Ζ) (t : Ty Δ κ) :
    rename ρ (subst σ t) =
      subst (fun {_} x => rename ρ (σ x)) t := by
  induction t generalizing Ε Ζ with
  | var => rfl
  | app f a ihf iha | arr f a ihf iha => simp [rename, subst, ihf, iha]
  | lam b ih | all b ih =>
    simp only [rename, subst]
    congr 1
    rw [ih]
    apply subst_congr
    intro ν x
    cases x with
    | zero => rfl
    | succ x =>
      simp only [liftSub, rename_rename]
      apply rename_congr
      intro ξ y
      rfl

/-- **Composition of simultaneous type-operator substitutions.**
Capture-avoiding simultaneous substitutions compose. -/
theorem subst_subst (σ : Sub Δ Ε) (τ : Sub Ε Ζ) (t : Ty Δ κ) :
    subst τ (subst σ t) =
      subst (fun {_} x => subst τ (σ x)) t := by
  induction t generalizing Ε Ζ with
  | var => rfl
  | app f a ihf iha | arr f a ihf iha => simp [subst, ihf, iha]
  | lam b ih | all b ih =>
    simp only [subst]
    congr 1
    rw [ih]
    apply subst_congr
    intro ν x
    cases x with
    | zero => rfl
    | succ x => simp only [liftSub, subst_rename, rename_subst]

/-- **Instantiating a weakened type operator leaves it unchanged.**
Discharging a fresh binder leaves a weakened operator unchanged. -/
@[simp] theorem instantiate_rename_succ (t : Ty Δ κ) (a : Ty Δ μ) :
    instantiate (rename KVar.succ t) a = t := by
  rw [instantiate, subst_rename]
  exact subst_id t

/-- **Substitution commutes with type-binder instantiation.**
Simultaneous substitution commutes with discharging a type binder. -/
theorem subst_instantiate (σ : Sub Δ Ε)
    (b : Ty (μ :: Δ) κ) (a : Ty Δ μ) :
    subst σ (instantiate b a) =
      instantiate (subst (liftSub σ) b) (subst σ a) := by
  simp only [instantiate, subst_subst]
  apply subst_congr
  intro ν x
  cases x with
  | zero => rfl
  | succ x => exact (instantiate_rename_succ (σ x) (subst σ a)).symm

/-- **Renaming commutes with type-binder instantiation.**
Renaming commutes with discharging a type binder. -/
theorem rename_instantiate (ρ : KRen Δ Ε)
    (b : Ty (μ :: Δ) κ) (a : Ty Δ μ) :
    rename ρ (instantiate b a) =
      instantiate (rename (KRen.lift ρ) b) (rename ρ a) := by
  simp only [instantiate, rename_subst, subst_rename]
  apply subst_congr
  intro ν x
  cases x <;> rfl

/-- **Renaming as substitution by variables.**
Renaming is substitution by the corresponding variable constructors. -/
theorem subst_var_rename (ρ : KRen Δ Ε) (t : Ty Δ κ) :
    subst (fun {_} x => .var (ρ x)) t = rename ρ t := by
  induction t generalizing Ε with
  | var => rfl
  | app f a ihf iha | arr f a ihf iha => simp [subst, rename, ihf, iha]
  | lam b ih | all b ih =>
    simp only [subst, rename]
    congr 1
    rw [subst_congr (σ := liftSub (fun {_} x => .var (ρ x)))
      (τ := fun {_} x => .var (KRen.lift ρ x))
      (by intro ν x; cases x <;> rfl), ih]

/-- **Lifted substitution commutes with weakening.**
Lifted type substitution commutes with weakening past the new binder. -/
theorem subst_lift_rename (σ : Sub Δ Ε) (t : Ty Δ κ) :
    subst (liftSub (μ := μ) σ) (rename KVar.succ t) =
      rename KVar.succ (subst σ t) := by
  simp only [subst_rename, rename_subst]
  rfl

end Cslib.Languages.LambdaCalculus.FOmega.Ty
