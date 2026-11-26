/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.StlcExtended.Syntax

/-!
# Substitution for the extended simply typed lambda calculus

Simultaneous substitution on intrinsically typed terms, lifted under the binders of abstraction,
case analysis and `let`, together with single-variable instantiation, which the reduction rules
for application, case analysis and `let` use. Because variables are de Bruijn indices,
substitution is capture-avoiding: the image of a variable under a lifted substitution is weakened
past the new binder.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.StlcExtended

open scoped CslibStlcExtended

universe u

namespace Sub

/-- **Identity substitution.** For a context $\Gamma$, the identity substitution from $\Gamma$ to
$\Gamma$ sends each variable of $\Gamma$ to the term consisting of that variable alone. -/
def id {Base : Type u} {Γ : List (Ty Base)} : Sub Γ Γ := fun x ↦ .var x

/-- **Substitution induced by a renaming.** For a renaming $\rho$ from $\Gamma$ to $\Delta$, the
induced substitution from $\Gamma$ to $\Delta$ sends each variable $x$ of $\Gamma$ to the term
consisting of the variable $\rho(x)$ alone. -/
def ofRen {Base : Type u} {Γ Δ : List (Ty Base)} (ρ : Ren Γ Δ) : Sub Γ Δ :=
  fun x ↦ .var (ρ x)

/-- **Lifting a substitution under a binder.** Given a substitution $\sigma$ from $\Gamma$ to
$\Delta$ and a type $A$, its lift is the substitution from $A :: \Gamma$ to $A :: \Delta$ that
sends the newest variable to the term consisting of the newest variable alone, and sends the
successor of each variable $x$ of $\Gamma$ to the weakening of $\sigma(x)$ into $A :: \Delta$. -/
def lift {Base : Type u} {A : Ty Base} {Γ Δ : List (Ty Base)} (σ : Sub Γ Δ) :
    Sub (A :: Γ) (A :: Δ)
  | _, .zero => .var .zero
  | _, .succ x => Tm.weaken (σ x)

/-- **Single-variable substitution.** Given a term $a$ of type $A$ in $\Gamma$, the
single-variable substitution for $a$ is the substitution from $A :: \Gamma$ to $\Gamma$ that
sends the newest variable to $a$ and the successor of each variable $x$ of $\Gamma$ to the term
consisting of the variable $x$ alone. -/
def single {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} (a : Tm Γ A) : Sub (A :: Γ) Γ
  | _, .zero => a
  | _, .succ x => .var x

@[simp] theorem lift_zero {Base : Type u} {A : Ty Base} {Γ Δ : List (Ty Base)} (σ : Sub Γ Δ) :
    lift (A := A) σ .zero = .var .zero := rfl

@[simp] theorem lift_succ {Base : Type u} {A B : Ty Base} {Γ Δ : List (Ty Base)} (σ : Sub Γ Δ)
    (x : Var Γ B) : lift (A := A) σ (.succ x) = Tm.weaken (σ x) := rfl

@[simp] theorem single_zero {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} (a : Tm Γ A) :
    single a .zero = a := rfl

@[simp] theorem single_succ {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} (a : Tm Γ A)
    (x : Var Γ B) : single a (.succ x) = .var x := rfl

end Sub

namespace Tm

/-- **Simultaneous substitution.** Given a substitution $\sigma$ from $\Gamma$ to $\Delta$, the
result $t[\sigma]$ of applying $\sigma$ to a term $t$ of type $A$ in $\Gamma$ is the term of type
$A$ in $\Delta$ defined by recursion on $t$: a variable $x$ becomes $\sigma(x)$; under each
binder, that is in the body of an abstraction, in both branches of a case analysis and in the
body of a `let`, the substitution is replaced by its lift; every other former is substituted
componentwise. -/
@[simp] def subst {Base : Type u} :
    {Γ Δ : List (Ty Base)} → Sub Γ Δ → {A : Ty Base} → Tm Γ A → Tm Δ A
  | _, _, σ, _, .var x => σ x
  | _, _, σ, _, .lam body => .lam (subst (Sub.lift σ) body)
  | _, _, σ, _, .app f a => .app (subst σ f) (subst σ a)
  | _, _, _, _, .unit => .unit
  | _, _, σ, _, .pair a b => .pair (subst σ a) (subst σ b)
  | _, _, σ, _, .fst p => .fst (subst σ p)
  | _, _, σ, _, .snd p => .snd (subst σ p)
  | _, _, σ, _, .inl a => .inl (subst σ a)
  | _, _, σ, _, .inr b => .inr (subst σ b)
  | _, _, σ, _, .case s l r =>
      .case (subst σ s) (subst (Sub.lift σ) l) (subst (Sub.lift σ) r)
  | _, _, _, _, .tt => .tt
  | _, _, _, _, .ff => .ff
  | _, _, σ, _, .ite c t e => .ite (subst σ c) (subst σ t) (subst σ e)
  | _, _, σ, _, .letIn a b => .letIn (subst σ a) (subst (Sub.lift σ) b)

/-- **Substitution respects pointwise equality.** If two substitutions $\sigma$ and $\tau$ from
$\Gamma$ to $\Delta$ agree on every variable, then they send every term of $\Gamma$ to the same
term. -/
theorem subst_congr {Base : Type u} {B : Ty Base} {Γ Δ : List (Ty Base)} {σ τ : Sub Γ Δ}
    (h : ∀ {A} (x : Var Γ A), σ x = τ x) (t : Tm Γ B) : subst σ t = subst τ t := by
  induction t generalizing Δ with
  | var x => simp only [subst, h]
  | lam body ih =>
      simp only [subst]
      rw [ih (σ := Sub.lift σ) (τ := Sub.lift τ) fun x => by cases x <;> simp [h]]
  | app f a ihf iha => simp only [subst, ihf h, iha h]
  | unit => rfl
  | pair a b iha ihb => simp only [subst, iha h, ihb h]
  | fst p ih => simp only [subst, ih h]
  | snd p ih => simp only [subst, ih h]
  | inl a ih => simp only [subst, ih h]
  | inr b ih => simp only [subst, ih h]
  | case s l r ihs ihl ihr =>
      simp only [subst]
      rw [ihs h, ihl (σ := Sub.lift σ) (τ := Sub.lift τ) fun x => by cases x <;> simp [h],
        ihr (σ := Sub.lift σ) (τ := Sub.lift τ) fun x => by cases x <;> simp [h]]
  | tt => rfl
  | ff => rfl
  | ite c t e ihc iht ihe => simp only [subst, ihc h, iht h, ihe h]
  | letIn a b iha ihb =>
      simp only [subst]
      rw [iha h, ihb (σ := Sub.lift σ) (τ := Sub.lift τ) fun x => by cases x <;> simp [h]]

/-- **Substitution along the identity.** Applying the identity substitution to a term returns the
term unchanged. -/
@[simp] theorem subst_id {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} (t : Tm Γ A) :
    subst Sub.id t = t := by
  induction t with
  | var x => rfl
  | lam body ih =>
      simp only [subst]
      rw [subst_congr (τ := Sub.id) (fun x => by cases x <;> rfl) body, ih]
  | app f a ihf iha => simp only [subst, ihf, iha]
  | unit => rfl
  | pair a b iha ihb => simp only [subst, iha, ihb]
  | fst p ih => simp only [subst, ih]
  | snd p ih => simp only [subst, ih]
  | inl a ih => simp only [subst, ih]
  | inr b ih => simp only [subst, ih]
  | case s l r ihs ihl ihr =>
      simp only [subst]
      rw [ihs, subst_congr (τ := Sub.id) (fun x => by cases x <;> rfl) l, ihl,
        subst_congr (τ := Sub.id) (fun x => by cases x <;> rfl) r, ihr]
  | tt => rfl
  | ff => rfl
  | ite c t e ihc iht ihe => simp only [subst, ihc, iht, ihe]
  | letIn a b iha ihb =>
      simp only [subst]
      rw [iha, subst_congr (τ := Sub.id) (fun x => by cases x <;> rfl) b, ihb]

/-- **Substitution along a renaming.** Applying the substitution induced by a renaming $\rho$ to a
term is renaming the term along $\rho$. -/
theorem subst_ofRen {Base : Type u} {A : Ty Base} {Γ Δ : List (Ty Base)} (ρ : Ren Γ Δ)
    (t : Tm Γ A) : subst (Sub.ofRen ρ) t = rename ρ t := by
  induction t generalizing Δ with
  | var x => rfl
  | lam body ih =>
      simp only [subst, rename]
      rw [subst_congr (τ := Sub.ofRen (Var.lift ρ)) (fun x => by cases x <;> rfl) body,
        ih (ρ := Var.lift ρ)]
  | app f a ihf iha => simp only [subst, rename, ihf, iha]
  | unit => rfl
  | pair a b iha ihb => simp only [subst, rename, iha, ihb]
  | fst p ih => simp only [subst, rename, ih]
  | snd p ih => simp only [subst, rename, ih]
  | inl a ih => simp only [subst, rename, ih]
  | inr b ih => simp only [subst, rename, ih]
  | case s l r ihs ihl ihr =>
      simp only [subst, rename]
      rw [ihs, subst_congr (τ := Sub.ofRen (Var.lift ρ)) (fun x => by cases x <;> rfl) l,
        ihl (ρ := Var.lift ρ),
        subst_congr (τ := Sub.ofRen (Var.lift ρ)) (fun x => by cases x <;> rfl) r,
        ihr (ρ := Var.lift ρ)]
  | tt => rfl
  | ff => rfl
  | ite c t e ihc iht ihe => simp only [subst, rename, ihc, iht, ihe]
  | letIn a b iha ihb =>
      simp only [subst, rename]
      rw [iha, subst_congr (τ := Sub.ofRen (Var.lift ρ)) (fun x => by cases x <;> rfl) b,
        ihb (ρ := Var.lift ρ)]

/-- **Instantiating a binder body.** Given a term $t$ of type $B$ in $A :: \Gamma$ and a term $a$
of type $A$ in $\Gamma$, the instantiation of $t$ with $a$ is the term of type $B$ in $\Gamma$
obtained by applying to $t$ the single-variable substitution for $a$, which replaces the newest
variable by $a$ and leaves the older variables unchanged. -/
def instantiate {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} (body : Tm (A :: Γ) B)
    (a : Tm Γ A) : Tm Γ B :=
  subst (Sub.single a) body

end Tm

end Cslib.Languages.LambdaCalculus.StlcExtended
