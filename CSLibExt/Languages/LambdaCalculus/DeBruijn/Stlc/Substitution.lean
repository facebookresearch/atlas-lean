/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Renaming and substitution for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Syntax

/-!
# Renaming and substitution for STLC

The algebra in this file is the infrastructure used by beta reduction.  The
fusion laws make explicit that lifting under binders commutes with renaming and
substitution.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Ξ : List (Ty Base)}

namespace Sub

/-- **Identity substitution (simply typed lambda calculus).** For a context $\Gamma$, the identity
substitution from $\Gamma$ to $\Gamma$ sends each variable of $\Gamma$ to the term consisting of
that variable alone. -/
def id : Sub Γ Γ := fun x ↦ .var x

/-- **Substitution induced by a renaming (simply typed lambda calculus).** For contexts $\Gamma$
and $\Delta$ and a type-preserving renaming $\rho$ from $\Gamma$ to $\Delta$, the induced
substitution from $\Gamma$ to $\Delta$ sends each variable $x$ of $\Gamma$ to the term consisting
of the variable $\rho(x)$ alone. -/
def ofRen (ρ : Ren Γ Δ) : Sub Γ Δ := fun x ↦ .var (ρ x)

/-- **Lifting a substitution under a binder (simply typed lambda calculus).** Write $A :: \Gamma$
for the context $\Gamma$ extended by a newest variable of type $A$. Given a substitution $\sigma$
from a context $\Gamma$ to a context $\Delta$ and a type $A$, its lift is the substitution from
$A :: \Gamma$ to $A :: \Delta$ that sends the newest variable to the term consisting of the
newest variable alone, and sends the successor of each variable $x$ of $\Gamma$ to the weakening
of the term $\sigma(x)$ into the context $A :: \Delta$. -/
def lift (σ : Sub Γ Δ) : Sub (A :: Γ) (A :: Δ)
  | _, .zero => .var .zero
  | _, .succ x => Tm.weaken (σ x)

/-- **Single-variable substitution (simply typed lambda calculus).** Write $A :: \Gamma$ for the
context $\Gamma$ extended by a newest variable of type $A$. Given a term $a$ of type $A$ in
context $\Gamma$, the single-variable substitution for $a$ is the substitution from
$A :: \Gamma$ to $\Gamma$ that sends the newest variable to $a$ and sends the successor of each
variable $x$ of $\Gamma$ to the term consisting of the variable $x$ alone. -/
def single (a : Tm Γ A) : Sub (A :: Γ) Γ
  | _, .zero => a
  | _, .succ x => .var x

@[simp] theorem lift_zero (σ : Sub Γ Δ) : lift (A := A) σ .zero = .var .zero := rfl

@[simp] theorem lift_succ (σ : Sub Γ Δ) (x : Var Γ B) :
    lift (A := A) σ (.succ x) = Tm.weaken (σ x) := rfl

@[simp] theorem single_zero (a : Tm Γ A) : single a .zero = a := rfl

@[simp] theorem single_succ (a : Tm Γ A) (x : Var Γ B) :
    single a (.succ x) = .var x := rfl

end Sub

namespace Tm

/-- **Simultaneous substitution (simply typed lambda calculus).** Given a substitution $\sigma$
from a context $\Gamma$ to a context $\Delta$, the result $t[\sigma]$ of applying $\sigma$ to a
term $t$ of type $A$ in context $\Gamma$ is the term of type $A$ in context $\Delta$ defined by
recursion on $t$: $x[\sigma] = \sigma(x)$ for a variable $x$,
$(f\,a)[\sigma] = f[\sigma]\,a[\sigma]$ for an application, and
$(\lambda u)[\sigma] = \lambda\,(u[\sigma'])$ for an abstraction with body $u$, where
$\sigma'$ is the lift of $\sigma$ under the binder. Because variables are de Bruijn indices, this
substitution is capture-avoiding. -/
def subst : {Γ Δ : List (Ty Base)} → Sub Γ Δ → {A : Ty Base} → Tm Γ A → Tm Δ A
  | _, _, σ, _, .var x => σ x
  | _, _, σ, _, .app f a => .app (subst σ f) (subst σ a)
  | _, _, σ, _, .lam body => .lam (subst (Sub.lift σ) body)

@[simp] theorem subst_var (σ : Sub Γ Δ) (x : Var Γ A) : subst σ (.var x) = σ x := rfl

@[simp] theorem subst_app (σ : Sub Γ Δ) (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    subst σ (.app f a) = .app (subst σ f) (subst σ a) := rfl

@[simp] theorem subst_lam (σ : Sub Γ Δ) (body : Tm (A :: Γ) B) :
    subst σ (.lam body) = .lam (subst (Sub.lift σ) body) := rfl

theorem subst_congr {σ τ : Sub Γ Δ} (h : ∀ {A} (x : Var Γ A), σ x = τ x)
    (t : Tm Γ B) : subst σ t = subst τ t := by
  induction t generalizing Δ with
  | var x => simp [h]
  | app f a ihf iha => simp [ihf h, iha h]
  | @lam A B Γ body ih =>
      simp only [subst_lam]
      congr 1
      apply ih
      intro C x
      cases x with
      | zero => rfl
      | succ x => simp [h]

@[simp] theorem subst_id (t : Tm Γ A) : subst Sub.id t = t := by
  induction t with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [subst_lam]
      have hlift : subst (Sub.lift (A := A) (Sub.id : Sub Γ Γ)) body =
          subst Sub.id body := subst_congr (fun x ↦ by cases x <;> rfl) body
      rw [hlift, ih]

theorem subst_ofRen (ρ : Ren Γ Δ) (t : Tm Γ A) :
    subst (Sub.ofRen ρ) t = rename ρ t := by
  induction t generalizing Δ with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [subst_lam, rename_lam]
      have hlift : subst (Sub.lift (A := A) (Sub.ofRen ρ)) body =
          subst (Sub.ofRen (Var.lift ρ)) body :=
        subst_congr (fun x ↦ by cases x <;> rfl) body
      rw [hlift, ih (ρ := Var.lift ρ)]

/-- **Instantiating a binder body (simply typed lambda calculus).** Write $A :: \Gamma$ for the
context $\Gamma$ extended by a newest variable of type $A$. Given a term $t$ of type $B$ in
context $A :: \Gamma$ and a term $a$ of type $A$ in context $\Gamma$, the instantiation of $t$
with $a$ is the term of type $B$ in context $\Gamma$ obtained by applying to $t$ the
single-variable substitution for $a$, which replaces the newest variable by $a$ and leaves the
older variables unchanged. -/
def instantiate (body : Tm (A :: Γ) B) (a : Tm Γ A) : Tm Γ B :=
  subst (Sub.single a) body

end Tm

end Cslib.Languages.LambdaCalculus.Stlc
