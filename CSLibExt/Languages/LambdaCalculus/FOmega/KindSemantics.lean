/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Binding

/-! # Semantic kind interpretation and substitution

The carrier at `star` is an arbitrary kind algebra. Later relational semantics
instantiates it with the existing System F relation carrier. Higher kinds are
actual function spaces; no typing or parametricity theorem is an algebra law.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

universe u

/-- Interpret kinds over a carrier for term types. -/
def Kind.Sem (α : Type u) : Kind → Type u
  | .star => α
  | .arrow κ μ => Kind.Sem α κ → Kind.Sem α μ

/-- An environment supplies a value of the declared kind for every variable. -/
abbrev KEnv (α : Type u) (Δ : List Kind) :=
  ∀ {κ}, KVar Δ κ → Kind.Sem α κ

/-- Extend a semantic environment at its newest kinded variable. -/
def KEnv.extend {α : Type u} {Δ : List Kind} {κ : Kind}
    (ρ : KEnv α Δ) (a : Kind.Sem α κ) : KEnv α (κ :: Δ)
  | _, .zero => a
  | _, .succ x => ρ x

/-- The two type constructors at `star`; higher kinds need no extra laws. -/
structure KindAlgebra (α : Type u) where
  arr : α → α → α
  all : {κ : Kind} → (Kind.Sem α κ → α) → α

namespace Ty

variable {α : Type u} {Δ Ε : List Kind} {κ μ : Kind}

/-- Interpret a kinded operator by ordinary function abstraction/application. -/
def eval (M : KindAlgebra α) : {Δ : List Kind} → KEnv α Δ →
    {κ : Kind} → Ty Δ κ → Kind.Sem α κ
  | _, ρ, _, .var x => ρ x
  | _, ρ, _, .lam b => fun a => eval M (KEnv.extend ρ a) b
  | _, ρ, _, .app f a => eval M ρ f (eval M ρ a)
  | _, ρ, _, .arr a b => M.arr (eval M ρ a) (eval M ρ b)
  | _, ρ, _, .all b => M.all (fun a => eval M (KEnv.extend ρ a) b)

/-- Interpretation depends only on the pointwise kinded environment. -/
theorem eval_congr (M : KindAlgebra α) {ρ τ : KEnv α Δ}
    (h : ∀ {ν} (x : KVar Δ ν), ρ x = τ x) (t : Ty Δ κ) :
    eval M ρ t = eval M τ t := by
  have e : @ρ = @τ := by funext ν x; exact h x
  rw [e]

/-- Semantic renaming is precomposition of the kinded environment. -/
theorem eval_rename (M : KindAlgebra α) (η : KEnv α Ε)
    (ρ : KRen Δ Ε) (t : Ty Δ κ) :
    eval M η (rename ρ t) = eval M (fun {_} x => η (ρ x)) t := by
  induction t generalizing Ε with
  | var => rfl
  | app f a ihf iha => simp [eval, rename, ihf, iha]
  | arr f a ihf iha =>
    simp only [eval, rename, ihf, iha]
    rfl
  | lam b ih =>
    funext a
    simp only [eval, rename, ih]
    apply eval_congr
    intro ν x
    cases x <;> rfl
  | all b ih =>
    simp only [eval, rename]
    congr 1
    funext a
    rw [ih]
    apply eval_congr
    intro ν x
    cases x <;> rfl

private theorem eval_liftSub (M : KindAlgebra α) (η : KEnv α Ε)
    (σ : Sub Δ Ε) (a : Kind.Sem α μ) {ν : Kind}
    (x : KVar (μ :: Δ) ν) :
    eval M (KEnv.extend η a) (liftSub σ x) =
      KEnv.extend (fun {_} y => eval M η (σ y)) a x := by
  cases x with
  | zero => rfl
  | succ x => exact eval_rename M (KEnv.extend η a) KVar.succ (σ x)

/-- Semantic simultaneous substitution at every kind, including higher kinds. -/
theorem eval_subst (M : KindAlgebra α) (η : KEnv α Ε)
    (σ : Sub Δ Ε) (t : Ty Δ κ) :
    eval M η (subst σ t) =
      eval M (fun {_} x => eval M η (σ x)) t := by
  induction t generalizing Ε with
  | var => rfl
  | app f a ihf iha => simp [eval, subst, ihf, iha]
  | arr f a ihf iha =>
    simp only [eval, subst, ihf, iha]
    rfl
  | lam b ih =>
    funext a
    simp only [eval, subst, ih]
    exact eval_congr M (fun x => eval_liftSub M η σ a x) b
  | all b ih =>
    simp only [eval, subst]
    congr 1
    funext a
    rw [ih]
    exact eval_congr M (fun x => eval_liftSub M η σ a x) b

/-- Semantic instantiation is environment extension by the argument value. -/
theorem eval_instantiate (M : KindAlgebra α) (η : KEnv α Δ)
    (b : Ty (μ :: Δ) κ) (a : Ty Δ μ) :
    eval M η (instantiate b a) =
      eval M (KEnv.extend η (eval M η a)) b := by
  rw [instantiate, eval_subst]
  apply eval_congr
  intro ν x
  cases x <;> rfl

end Ty

end Cslib.Languages.LambdaCalculus.FOmega
